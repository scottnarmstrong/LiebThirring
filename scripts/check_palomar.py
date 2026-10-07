#!/usr/bin/env python3
"""Offline Palomar preparation checks (policy 96b034c; never runs submitted code).

Usage: python3 -I scripts/check_palomar.py --root TREE [--schema v0.4.schema.json]
Use --comparator PATH repeatedly to select arbitrary JSON filenames. Otherwise
discover comparator.json and JSON objects with challenge_module/solution_module.
The default scans the working tree, including untracked files, excluding .git
and .lake. --tracked scans the Git index instead. No builds, downloads, writes,
or package installation. Optional installed PyYAML/jsonschema improve validation;
without them a deliberately bounded YAML reader and field checks are used.
TODO means either a defect or a check requiring evidence this tool cannot supply.
Exit 1 for local defects, 0 for locally passing checks (review TODOs may remain).
This is preparation evidence, never a Palomar mechanical verification report.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import runpy
import subprocess
import sys

POLICY = "96b034cc31a72a63d4f4041911dce337a85c9a04"
GITHUB = re.compile(r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:\.git)?")
SHA = re.compile(r"[0-9a-f]{40}")
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
ARTIFACTS = {".olean", ".ilean", ".a", ".bc", ".dll", ".dylib", ".o", ".obj", ".so", ".trace"}
LICENSE = re.compile(r"(?:LICENSE|LICENCE|COPYING|UNLICENSE|OFL)(?:\.(?:md|markdown|txt))?", re.I)
LOCAL_HELPERS = Path(__file__).resolve().parents[1] / "scripts/check_lean_modules.py"


def pairs(items):
    out = {}
    for key, value in items:
        if key in out or key == "<<":
            raise ValueError(f"duplicate or merge key: {key}")
        out[key] = value
    return out


def unquote_comment(text):
    """Remove YAML comments outside quoted strings; retain quoted punctuation."""
    quote, escaped = None, False
    for i, char in enumerate(text):
        if escaped:
            escaped = False
        elif char == "\\" and quote == '"':
            escaped = True
        elif char == quote:
            quote = None
        elif quote is None and char in "\"'":
            quote = char
        elif quote is None and char == "#" and (i == 0 or text[i - 1].isspace()):
            return text[:i].rstrip()
    return text.rstrip()


def scalar(text):
    text = text.strip()
    if text.startswith('"'):
        return json.loads(text)
    if text.startswith("'"):
        if not text.endswith("'") or len(text) < 2:
            raise ValueError("unterminated quoted YAML scalar")
        return text[1:-1].replace("''", "'")
    if text.startswith(("[", "{")):
        # JSON is YAML; the other supported flow form is a flat scalar list.
        try:
            return json.loads(text, object_pairs_hook=pairs)
        except json.JSONDecodeError:
            if not text.startswith("[") or not text.endswith("]"):
                raise ValueError("unsupported YAML flow mapping/list; use JSON or block YAML")
            inner = text[1:-1]
            parts = re.split(r",(?=(?:[^\"']|\"[^\"]*\"|'[^']*')*$)", inner)
            return [scalar(p) for p in parts] if inner.strip() else []
    if re.search(r"(^|\s)[&*!]|:\s|[\[\]{}]", text):
        raise ValueError("unsupported YAML scalar/anchor/tag; install an offline YAML parser")
    if text in {"null", "~", ""}:
        return None
    if text in {"true", "false"}:
        return text == "true"
    if re.fullmatch(r"[-+]?(?:0|[1-9][0-9]*)", text):
        return int(text)
    if re.fullmatch(r"[-+]?[0-9]+\.[0-9]+", text):
        return float(text)
    return text


def minimal_yaml(text):
    """Common metadata subset: block mappings/lists, flat flow lists, > and |.

    Reject unsupported syntax rather than silently accepting a malformed file.
    This is a field-level fallback, not a general YAML conformance validator.
    """
    try:
        return json.loads(text, object_pairs_hook=pairs)
    except json.JSONDecodeError:
        pass
    lines = []
    for number, raw in enumerate(text.splitlines(), 1):
        if "\t" in raw[:len(raw) - len(raw.lstrip())]:
            raise ValueError(f"line {number}: tab indentation")
        value = unquote_comment(raw.lstrip())
        if not value:
            continue
        if value in {"---", "..."} or value.startswith("%"):
            raise ValueError("YAML document markers/directives need an offline YAML parser")
        lines.append((len(raw) - len(raw.lstrip()), value, number, raw))

    def block(index, indent):
        sequence = lines[index][1].startswith("- ") or lines[index][1] == "-"
        result = [] if sequence else {}

        def item(value, next_index, child_indent):
            if value in {">", ">-", ">+", "|", "|-", "|+"}:
                fragments = []
                while next_index < len(lines) and lines[next_index][0] >= child_indent:
                    fragments.append(lines[next_index][3].strip())
                    next_index += 1
                separator = " " if value.startswith(">") else "\n"
                return separator.join(fragments) + ("" if value.endswith("-") else "\n"), next_index
            if value:
                return scalar(value), next_index
            if next_index < len(lines) and lines[next_index][0] >= child_indent:
                return block(next_index, lines[next_index][0])
            return None, next_index

        while index < len(lines) and lines[index][0] == indent:
            _, content, number, _ = lines[index]
            index += 1
            if sequence:
                if not (content == "-" or content.startswith("- ")):
                    raise ValueError(f"line {number}: mixed YAML sequence/mapping")
                value = content[1:].lstrip()
                if re.match(r"[A-Za-z_][A-Za-z0-9_.-]*:\s|[A-Za-z_][A-Za-z0-9_.-]*:$", value):
                    key, val = value.split(":", 1)
                    child, index = item(val.strip(), index, indent + 4)
                    entry = {key: child}
                    if index < len(lines) and lines[index][0] == indent + 2:
                        extra, index = block(index, indent + 2)
                        if not isinstance(extra, dict):
                            raise ValueError("expected mapping continuation")
                        entry = pairs([*entry.items(), *extra.items()])
                    result.append(entry)
                else:
                    child, index = item(value, index, indent + 2)
                    result.append(child)
            else:
                match = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_.-]*|<<):(?:\s+(.*))?", content)
                if not match:
                    raise ValueError(f"line {number}: unsupported YAML mapping syntax")
                key, val = match.group(1), match.group(2) or ""
                if key in result or key == "<<":
                    raise ValueError(f"line {number}: duplicate or merge key {key}")
                result[key], index = item(val, index, indent + 1)
        return result, index

    if not lines:
        return None
    if lines[0][0] != 0:
        raise ValueError("top-level YAML must start at indentation zero")
    result, index = block(0, 0)
    if index != len(lines):
        raise ValueError(f"line {lines[index][2]}: unexpected indentation")
    return result


def load_yaml(text):
    if importlib.util.find_spec("yaml") is None:
        return minimal_yaml(text), "stdlib field-level YAML subset"
    import yaml  # optional installed offline; no dependency installation

    class StrictLoader(yaml.SafeLoader):
        pass

    def mapping(loader, node):
        return pairs([(loader.construct_object(k), loader.construct_object(v)) for k, v in node.value])

    StrictLoader.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, mapping)
    try:
        return yaml.load(text, Loader=StrictLoader), "offline PyYAML (duplicate/merge keys rejected)"
    except yaml.YAMLError as exc:
        raise ValueError(f"invalid YAML: {exc}") from exc


def field_errors(data, schema, path="$"):
    """Field-level schema subset; not a full JSON Schema validator."""
    errors = []
    types = {"object": dict, "array": list, "string": str, "integer": int, "number": (int, float), "boolean": bool}
    expected = schema.get("type")
    if expected:
        expected = expected if isinstance(expected, list) else [expected]
        good = any(isinstance(data, types[t]) and not (t in {"integer", "number"} and isinstance(data, bool)) for t in expected)
        if not good:
            return [f"{path}: expected {'/'.join(expected)}"]
    if "enum" in schema and data not in schema["enum"]:
        errors.append(f"{path}: not in allowed vocabulary {schema['enum']}")
    if isinstance(data, dict):
        errors += [f"{path}.{key}: required field missing" for key in schema.get("required", []) if key not in data]
        for key, child in schema.get("properties", {}).items():
            if key in data:
                errors += field_errors(data[key], child, f"{path}.{key}")
    if isinstance(data, list):
        if len(data) < schema.get("minItems", 0):
            errors.append(f"{path}: list too short")
        for i, value in enumerate(data):
            errors += field_errors(value, schema.get("items", {}), f"{path}[{i}]")
    if isinstance(data, str) and len(data) < schema.get("minLength", 0):
        errors.append(f"{path}: string too short")
    if isinstance(data, (int, float)) and "minimum" in schema and data < schema["minimum"]:
        errors.append(f"{path}: below minimum")
    return errors


class Check:
    def __init__(self, root):
        self.root, self.rows, self.bad = root, [], False

    def report(self, name, errors=(), note="", review=False):
        errors = list(errors)
        self.bad |= bool(errors) and not review
        self.rows.append({"check": name, "status": "TODO" if errors or review else "PASS", "detail": "; ".join(errors) or note})

    def file(self, relative, limit):
        path = self.root / relative
        if not path.is_relative_to(self.root) or any(part in {"", ".", ".."} for part in relative.split("/")) or re.search(r"[\\?#:\x00-\x1f\x7f]", relative):
            raise ValueError(f"{relative}: unsafe repository-relative path")
        cursor = path
        while cursor != self.root:
            if cursor.is_symlink():
                raise ValueError(f"{relative}: symlink path component")
            cursor = cursor.parent
        if not path.is_file() or path.stat().st_size > limit:
            raise ValueError(f"{relative}: missing regular file or exceeds {limit} bytes")
        return path.read_bytes().decode("utf-8")


def inventory(root, tracked):
    if tracked:
        result = subprocess.run(["git", "ls-files", "-z"], cwd=root, capture_output=True, check=True)
        return [root / n for n in result.stdout.decode().split("\0") if n and not {".git", ".lake"}.intersection(Path(n).parts)]
    files = []
    for directory, dirs, names in os.walk(root, followlinks=False):
        dirs[:] = sorted(d for d in dirs if d not in {".git", ".lake"})
        files += [Path(directory) / n for n in sorted(names)]
        files += [Path(directory) / d for d in dirs if (Path(directory) / d).is_symlink()]
        dirs[:] = [d for d in dirs if not (Path(directory) / d).is_symlink()]
    return sorted(files)


def metadata_checks(c, data, license_id):
    errors = []

    def get(path, default=None):
        value = data
        for part in path.split("."):
            if not isinstance(value, dict):
                return default
            value = value.get(part, default)
        return value

    def nonempty(value):
        return isinstance(value, str) and bool(value.strip())

    def names(value):
        return isinstance(value, list) and bool(value) and all(nonempty(x) or isinstance(x, dict) and nonempty(x.get("name")) for x in value)

    if not isinstance(data, dict):
        c.report("metadata fields", ["one top-level mapping required"])
        return
    if data.get("version", "v0.4") != "v0.4":
        errors.append("use version v0.4 for the adopted Palomar format")
    for field, limit in [("project.name", 300), ("project.description", 10000)]:
        value = get(field)
        if not nonempty(value) or len(value) > limit:
            errors.append(f"{field}: nonempty string <= {limit} characters required")
    if not names(get("project.authors")):
        errors.append("project.authors: nonempty human name list required")
    project = get("project", {})
    if not isinstance(project, dict):
        project = {}
    maintainers = project.get("responsible_maintainers", project.get("responsible_maintainer")) if isinstance(project, dict) else None
    if "responsible_maintainers" not in project and isinstance(maintainers, (str, dict)):
        maintainers = [maintainers]
    if not names(maintainers):
        errors.append("project.responsible_maintainers: nonempty human name list required")
    if not nonempty(get("project.license")) or license_id and get("project.license") != license_id:
        errors.append("project.license: missing or differs from root license")
    for field, minimum in [("arxiv", 1), ("msc2020", 0)]:
        codes = get("classification." + field, [] if field == "msc2020" else None)
        if not isinstance(codes, list) or not minimum <= len(codes) <= 8 or not all(nonempty(x) for x in codes) or len(set(codes)) != len(codes):
            errors.append(f"classification.{field}: {minimum}..8 distinct code strings required")
    methods = get("automation.methods")
    if not isinstance(methods, list) or not methods or not all(isinstance(m, dict) and nonempty(m.get("method")) for m in methods):
        errors.append("automation.methods: nonempty mappings with method required")
    if not nonempty(get("review.status")):
        errors.append("review.status: nonempty pre-submission review status required")
    sources = get("sources")
    relationships = {"formalizes", "adapts", "independently-proves", "background", "other"}
    source_types = {"paper", "book", "web discussion", "folklore", "original-proof", "other"}
    if not isinstance(sources, list) or not sources:
        errors.append("sources: nonempty source list required")
        sources = []
    for i, source in enumerate(sources):
        if not isinstance(source, dict):
            errors.append(f"sources[{i}]: mapping required")
            continue
        if not nonempty(source.get("title")) or source.get("relationship") not in relationships:
            errors.append(f"sources[{i}]: title and canonical relationship required")
        if "type" in source and source["type"] not in source_types:
            errors.append(f"sources[{i}].type: not in closed policy vocabulary")
        for person in source.get("contributors", []) if isinstance(source.get("contributors", []), list) else [None]:
            if not isinstance(person, dict) or not nonempty(person.get("name")) or not nonempty(person.get("role")) or len(person["role"]) > 200:
                errors.append(f"sources[{i}].contributors: nonempty name and role <= 200 characters required")
    sources = [s for s in sources if isinstance(s, dict)]
    original = [s for s in sources if s.get("type") == "original-proof"]
    if original:
        if any(s.get("relationship") != "other" for s in original) or any(s.get("relationship") not in {"background", "other"} for s in sources):
            errors.append("source origin: original-proof cannot coexist with substantive source relationships")
    elif not any(s.get("relationship") in {"formalizes", "adapts", "independently-proves"} for s in sources):
        errors.append("source origin: source-based result requires a substantive source relationship")
    repo = get("repository", {})
    if not isinstance(repo, dict):
        errors.append("repository: mapping required when present")
    else:
        underlying = repo.get("substantive_formalization")
        if repo.get("role") == "thin-wrapper" and underlying is None:
            errors.append("thin-wrapper requires substantive_formalization")
        if repo.get("role") == "substantive-development" and underlying is not None:
            errors.append("substantive-development forbids substantive_formalization")
        if underlying is not None:
            if not isinstance(underlying, dict) or not re.fullmatch(r"(?:https://github\.com/)?[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:\.git)?", str(underlying.get("id", ""))) or not SHA.fullmatch(str(underlying.get("revision", ""))):
                errors.append("substantive_formalization requires GitHub repository and lowercase full SHA")
            c.report("substantive repository", note="resolve public commit, scan its sources, LFS and submodules separately", review=True)
    c.report("metadata fields", errors, "Palomar structural fields and source-derived origin")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--tracked", action="store_true")
    parser.add_argument("--project", default="", help="selected project relative to repository root")
    parser.add_argument("--metadata", help="repository-relative formalization.yaml")
    parser.add_argument("--comparator", action="append", default=[])
    parser.add_argument("--schema", type=Path, help="offline v0.4 schema (or dispatcher with adjacent v0.4.schema.json)")
    parser.add_argument("--taxonomy-dir", type=Path, help="offline PalomarSubmission taxonomies directory")
    parser.add_argument("--minimum-toolchain", help="minimum release from pinned PalomarSubmission/toolchains.json")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    root = args.root.resolve()
    if not root.is_dir():
        parser.error("--root must be an existing directory")
    c = Check(root)
    try:
        project = root / args.project
        if args.project:
            c.file(args.project + "/lean-toolchain" if (project / "lean-toolchain").exists() else "lean-toolchain", 1024)
        if not project.is_dir() or not project.resolve().is_relative_to(root) or ".lake" in Path(args.project).parts:
            raise ValueError("selected project must be contained outside .lake")
        files = inventory(root, args.tracked)
        helpers = runpy.run_path(str(LOCAL_HELPERS), run_name="palomar_helpers")
        lean_errors = []
        lean_files = [p for p in files if p.suffix == ".lean"]
        for path in lean_files:
            rel = path.relative_to(root).as_posix()
            try:
                text = c.file(rel, 500 * 1024 * 1024)
                if path.name != "lakefile.lean" and not helpers["has_module_header"](text):
                    lean_errors.append(f"{rel}: missing module header")
                # Only LF/CRLF delimit physical lines; splitlines also counts Unicode separators.
                lines = text.count("\n") + bool(text and not text.endswith("\n"))
                if lines > 10000:
                    lean_errors.append(f"{rel}: {lines} physical lines > 10000")
            except (OSError, ValueError) as exc:
                lean_errors.append(str(exc))
        c.report("Lean sources", lean_errors, f"{len(lean_files)} files; reused module-header lexer, all working files unless --tracked")
        size, artifacts, lfs = 0, [], []
        for path in files:
            if path.is_symlink() or not path.is_file():
                continue
            size += path.stat().st_size
            if path.suffix.lower() in ARTIFACTS:
                artifacts.append(str(path.relative_to(root)))
            with path.open("rb") as stream:
                if stream.read(130).startswith(b"version https://git-lfs.github.com/spec/v1"):
                    lfs.append(str(path.relative_to(root)))
        # Generated .lake caches are irrelevant to a working-tree check, but
        # committed .lake objects count towards the submitted checkout size.
        indexed = subprocess.run(["git", "ls-files", "-z"], cwd=root, capture_output=True)
        if indexed.returncode == 0:
            for name in indexed.stdout.decode().split("\0"):
                path = root / name
                if name and ".lake" in Path(name).parts and path.is_file() and not path.is_symlink():
                    size += path.stat().st_size
        c.report("repository size", [] if size <= 500 * 1024 * 1024 else [f"{size} bytes > 500 MiB"], f"{size} regular-file bytes excluding .git/symlinks and untracked .lake caches; indexed .lake counted; final commit needs a fresh checkout")
        c.report("compiled artifacts / LFS", artifacts + lfs, "none in scanned submitted tree; dependency graph still requires verifier scan")
        git = subprocess.run(["git", "ls-files", "--stage"], cwd=root, capture_output=True, text=True)
        c.report("submodules", [line for line in git.stdout.splitlines() if line.startswith("160000 ")], "no Git-index gitlinks" if git.returncode == 0 else "not a Git checkout; inspect final commit", review=git.returncode != 0)
        prefix = args.project.rstrip("/") + "/" if args.project else ""
        lakefiles = [prefix + name for name in ["lakefile.lean", "lakefile.toml"] if (project / name).exists()]
        if len(lakefiles) != 1:
            c.report("Lakefile", ["selected project needs exactly one Lakefile"])
        else:
            lake_text = c.file(lakefiles[0], 1024 * 1024)
            if lakefiles[0].endswith(".toml"):
                import tomllib
                tomllib.loads(lake_text)
            c.report("Lakefile", note=lakefiles[0])
        toolpath = prefix + "lean-toolchain" if (project / "lean-toolchain").exists() else "lean-toolchain"
        toolchain = c.file(toolpath, 1024).strip()
        release = re.fullmatch(r"leanprover/lean4:v(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?", toolchain)
        c.report("toolchain shape", [] if release else ["must name a Lean release, including rc suffix when applicable"], toolchain)
        if args.minimum_toolchain and release:
            minimum = re.fullmatch(r"(?:leanprover/lean4:)?v?(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?", args.minimum_toolchain)
            if not minimum:
                raise ValueError("invalid --minimum-toolchain")
            key = lambda m: tuple(int(x) for x in m.groups()[:3]) + (int(m[4]) if m[4] else sys.maxsize,)
            c.report("minimum toolchain", [] if key(release) >= key(minimum) else ["release is older than minimum"], args.minimum_toolchain)
        else:
            c.report("minimum toolchain", note="supply --minimum-toolchain from current pinned verifier toolchains.json", review=True)
        manifests = [p for p in files if p.name == "lake-manifest.json"]
        if project / "lake-manifest.json" not in manifests:
            c.report("manifest", ["commit selected project's manifest (TOML exception requires separate review)"])
        for path in manifests:
            rel = path.relative_to(root).as_posix()
            manifest = json.loads(c.file(rel, 500 * 1024 * 1024), object_pairs_hook=pairs)
            errors = []
            if not isinstance(manifest, dict) or not isinstance(manifest.get("packages"), list):
                c.report(rel, ["manifest object with packages list required"])
                continue
            for package in manifest["packages"]:
                if not isinstance(package, dict):
                    errors.append("package must be an object")
                    continue
                name = package.get("name", "?")
                if package.get("type") == "git":
                    if not GITHUB.fullmatch(str(package.get("url", ""))) or not SHA.fullmatch(str(package.get("rev", ""))):
                        errors.append(f"{name}: public credential-free GitHub URL and lowercase full SHA required")
                    if name == "mathlib" and package.get("url", "").removesuffix(".git") == "https://github.com/leanprover-community/mathlib4":
                        dep = path.parent / manifest.get("packagesDir", ".lake/packages") / "mathlib"
                        actual = subprocess.run(["git", "-C", str(dep), "show", f"{package.get('rev')}:lean-toolchain"], capture_output=True, text=True)
                        if actual.returncode == 0:
                            c.report("Mathlib toolchain " + rel, [] if actual.stdout.strip() == toolchain else ["resolved Mathlib commit's toolchain differs"], actual.stdout.strip())
                        else:
                            c.report("Mathlib toolchain " + rel, note="resolved commit unavailable offline; authenticate canonical source and compare exact toolchain", review=True)
                elif package.get("type") == "path":
                    target = path.parent / str(package.get("dir", ""))
                    if not target.resolve().is_relative_to(root) or target.resolve() == path.parent or ".lake" in target.relative_to(root).parts or target.is_symlink() or not target.is_dir():
                        errors.append(f"{name}: path target must be distinct, contained, regular and outside .lake")
                    c.report("contained dependency " + str(name), note="review target Lakefile/manifest, every path component, packagesDir ownership and package-name overlap (§6.3–6.4)", review=True)
                else:
                    errors.append(f"{name}: unknown package type")
            c.report(rel, errors, f"{len(manifest['packages'])} dependency pin shapes checked")
        licenses = [p for p in root.iterdir() if LICENSE.fullmatch(p.name)]
        license_id = None
        if len(licenses) != 1:
            c.report("root license", ["exactly one accepted conventional license filename required"])
        else:
            license_text = c.file(licenses[0].name, 1024 * 1024)
            if not license_text.strip():
                c.report("root license", ["nonempty UTF-8 license required"])
            else:
                # Recognise this project's complete standard Apache terms, not an SPDX comment alone.
                if "Apache License" in license_text and "Version 2.0, January 2004" in license_text and "END OF TERMS AND CONDITIONS" in license_text:
                    license_id = "Apache-2.0"
                c.report("root license file", note=f"{licenses[0].name}; candidate {license_id or 'not locally recognised'}")
                c.report("SPDX license detection", note="Palomar's authoritative detector must identify exactly one SPDX license; local Apache recognition is only a hint", review=True)
        metadata_path = args.metadata or prefix + "formalization.yaml"
        if Path(metadata_path).name != "formalization.yaml":
            raise ValueError("metadata basename must be formalization.yaml")
        data = None
        try:
            data, mode = load_yaml(c.file(metadata_path, 256 * 1024))
            c.report("metadata parse", note=mode)
            metadata_checks(c, data, license_id)
            if args.schema:
                schema_path = args.schema
                schema = json.loads(schema_path.read_text())
                if schema.get("title") == "formalization.yaml (version dispatcher)":
                    schema = json.loads((schema_path.parent / "v0.4.schema.json").read_text())
                if "$ref" in json.dumps(schema):
                    raise ValueError("offline schema must be self-contained (no remote resolution)")
                if importlib.util.find_spec("jsonschema") is not None:
                    import jsonschema
                    validator = jsonschema.validators.validator_for(schema)
                    validator.check_schema(schema)
                    errors = [f"{list(e.path)}: {e.message}" for e in validator(schema).iter_errors(data)]
                    c.report("upstream schema", errors, "offline full JSON Schema validation")
                else:
                    c.report("upstream schema fields", field_errors(data, schema), "stdlib types/required/enum/length/nonnegative fields; conditional repository rules checked separately")
            else:
                c.report("upstream schema", note="supply --schema for upstream optional-field checks", review=True)
        except (OSError, ValueError) as exc:
            c.report("metadata", [str(exc)])
        if args.taxonomy_dir and isinstance(data, dict):
            for key, filename in [("arxiv", "arxiv-categories.json"), ("msc2020", "msc2020-codes.json")]:
                taxonomy = json.loads((args.taxonomy_dir / filename).read_text())
                # Avoid guessing snapshot formats: accept explicit code maps or code-bearing records.
                known = set(taxonomy) if isinstance(taxonomy, dict) else {r if isinstance(r, str) else r.get("code") for r in taxonomy}
                codes = data.get("classification", {}).get(key, [])
                c.report("taxonomy " + key, [str(x) + ": unknown code" for x in codes if x not in known], filename)
        else:
            c.report("classification code existence", note="supply --taxonomy-dir from pinned PalomarSubmission; formatting cannot establish taxonomy membership", review=True)
        configs = list(args.comparator)
        if not configs:
            for path in files:
                if path.suffix == ".json" and path.resolve().is_relative_to(project.resolve()) and not path.is_symlink():
                    try:
                        candidate = json.loads(path.read_text())
                        if path.name == "comparator.json" or isinstance(candidate, dict) and ("challenge_module" in candidate or "solution_module" in candidate):
                            configs.append(path.relative_to(root).as_posix())
                    except (ValueError, UnicodeError):
                        if path.name == "comparator.json":
                            configs.append(path.relative_to(root).as_posix())
        if not configs:
            c.report("Comparator configuration", ["no configuration found; use --comparator for an arbitrary JSON filename"])
        for rel in configs:
            try:
                errors = []
                if not rel.endswith(".json") or not (root / rel).resolve().is_relative_to(project.resolve()):
                    raise ValueError("Comparator path must be a JSON file inside selected project")
                config = json.loads(c.file(rel, 1024 * 1024), object_pairs_hook=pairs)
                required = {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
                if not isinstance(config, dict):
                    raise ValueError("Comparator config must be one JSON object")
                if not required <= config.keys() or config.keys() - required - {"definition_names", "enable_nanoda"}:
                    errors.append("missing required or unknown configuration keys")
                for key in ["theorem_names", "definition_names"]:
                    names = config.get(key, [] if key == "definition_names" else None)
                    if not isinstance(names, list) or key == "theorem_names" and not names or not all(isinstance(n, str) and n.strip() for n in names):
                        errors.append(f"{key}: nonempty name strings required; theorem list nonempty")
                axioms = config.get("permitted_axioms")
                if not isinstance(axioms, list) or not all(isinstance(a, str) and a in AXIOMS for a in axioms):
                    errors.append("permitted_axioms: only propext, Quot.sound, Classical.choice")
                if config.get("challenge_module") == config.get("solution_module"):
                    errors.append("Challenge and Solution must be distinct")
                for key in ["challenge_module", "solution_module"]:
                    module = config.get(key)
                    if not isinstance(module, str) or not MODULE.fullmatch(module):
                        errors.append(f"{key}: invalid dotted module name")
                        continue
                    source = prefix + module.replace(".", "/") + ".lean"
                    if not (root / source).exists():
                        c.report(rel + " " + key, note=f"default source {source} missing; Lake ordered source paths must resolve it (not evaluated offline)", review=True)
                        continue
                    text = c.file(source, 500 * 1024 * 1024)
                    if key == "challenge_module":
                        lines, size = text.count("\n") + bool(text and not text.endswith("\n")), len(text.encode())
                        if lines > 1000 or size > 100 * 1024:
                            errors.append(f"Challenge {lines} lines/{size} bytes exceeds 1000 lines/100 KiB")
                        c.report(rel + " Challenge size", note=f"{lines} lines/{size} bytes" + ("; nonblocking audit-size warning (>300 lines or 32 KiB)" if lines > 300 or size > 32 * 1024 else ""))
                        code = helpers["code_mask"](text)
                        imports = re.findall(r"(?m)^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([^\n]+)", code)
                        bad_imports = [m for line in imports for m in line.split() if not (m == "Mathlib" or m.startswith(("Mathlib.", "Lean.", "Init.", "Std.")) or m in {"Lean", "Init", "Std"})]
                        local_imports = [m for m in bad_imports if (project / (m.replace(".", "/") + ".lean")).exists()]
                        if local_imports:
                            errors.append("Challenge imports project-specific source: " + ", ".join(local_imports))
                        c.report(rel + " direct Challenge imports", note="core/Mathlib names only" if not bad_imports else "verify approved Tau Ceti/CSLib or reject project-specific imports: " + ", ".join(bad_imports), review=bool(bad_imports))
                    # Imported/re-exported Solution declarations are legitimate. Do not demand local copies.
                c.report(rel, errors, "configuration shape; NanoDa switch optional and non-authoritative; one entry per configuration")
            except (OSError, ValueError) as exc:
                c.report(rel, [str(exc)])
        readmes = [p for p in [project / "README.md", root / "README.md"] if p.is_file() and not p.is_symlink()]
        c.report("narrative account", note="review Challenge docs, selected declarations, metadata and " + (str(readmes[0].relative_to(root)) if readmes else "README absent (README itself is not a hard intake requirement)"), review=True)
        c.report("external verification / editorial review", note="authenticate public revisions, full dependency/LFS/Challenge source closure, Lean parser headers, Lake source resolution, Comparator+NanoDa, Verso render and every rubric pass; not certified by this offline checker", review=True)
    except (OSError, ValueError, subprocess.SubprocessError, TypeError) as exc:
        c.report("input/scan", [str(exc)])
    result = {"policy_commit": POLICY, "root": str(root), "scope": "git-index" if args.tracked else "working-tree", "local_pass": not c.bad, "checks": c.rows}
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        for row in c.rows:
            print(f"{row['status']}: {row['check']}: {row['detail']}")
        print("check_palomar: " + ("FAIL (local defects)" if c.bad else "PASS (local checks only; review TODOs remain)"))
    return int(c.bad)


if __name__ == "__main__":
    sys.exit(main())
