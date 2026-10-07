# Redacted orchestrator transcript

`session.md` renders the user/assistant messages, reasoning, context attachments,
queued messages, tool calls and inputs in source order. Tool results longer than
6,000 characters have an explicit truncation marker; code fences preserve text
without interpreting embedded HTML or image links. Dollars outside fenced or
inline code are escaped to prevent accidental math rendering. `session.jsonl`
keeps every complete source record, its JSON structure and full tool results
after redaction.
String values (including object keys) may be replaced; binary attachment payloads
are omitted. Model usage token counts are preserved; account quota data is removed.

The source log was redacted recursively, including duplicate metadata and tool
inputs/outputs. Rules cover e-mail addresses; hostnames; home paths (`~` or
`<home>`); temporary CLI directories (`<tmp>`); account identifiers (`<account>`)
and account directories (`<accounts-dir>`); complete quota-command results and
quota tables/disclosures; other projects and unrelated tmux sessions; process
command lines mentioning other projects; usernames/groups in system listings;
credential values and private keys; and base64 image/document payloads.
Additional release rules redact private development-directory references and
integrity-tool names, including the private scratch directory, and remaining
absolute local-directory prefixes. Mathematics, Lean code and other project
material otherwise retain their source text.
Encoded home-directory slugs and complete URLs to unrelated local repositories
are masked too, including account prefixes; public dependency URLs are retained.
Privacy redactions use visible markers. The input log is private and is not
included in this repository.

The private-name inventory includes every top-level home directory entry (files,
directories and dotfiles), except this repository and its scratch directory, and
every live or logged tmux session whose name does not start with `lt-`. Generic
home-entry matching is case-sensitive; identified unrelated repository/project
names also match case-insensitively, including longer cache-name prefixes and
underscore suffixes. Those full name components are replaced; the specifically
named Mathlib-reference project uses `[another project]`. Public repository and
profile URLs retain GitHub usernames; unrelated repository URLs are removed
completely. `lt-` session names are preserved.

Standalone private e-mail local parts and `@` plus mail-domain fragments,
account-directory basename fragments, and non-English prefixes of private home
entry names with at least six characters are also removed. Known English words
are exempt from this extra prefix rule via a bundled word list; unlisted prefixes
are masked. Explicit unrelated skill/source terms and cleanup-directory fragments
are removed too. These additional rules use case-sensitive word boundaries.
Opaque base64 signatures remain byte-for-byte intact in the JSONL, are excluded
from privacy scans, and are omitted from Markdown. The exemption applies only
to explicitly named signature fields, including those inside quoted JSON.

From the directory containing `export_transcript.py`, regenerate and check with:

```sh
python3 -I export_transcript.py
python3 -I export_transcript.py --check
```

The default input is the designated session under the local account directories.
Use `--input PATH` for a relocated log, `--home PATH` for its original home, and
repeat `--private-name NAME` or `--hostname NAME` for additional private names.
The inventory is derived from the input and local home directory, never published.
`--check` scans both outputs (and this README), reports counts per rule and exits
nonzero on residual private patterns, invalid JSON or unescaped dollars outside
code. Checks use the source-derived
inventory, so retain access to the private input when checking. A concurrently
appended incomplete final record is deferred to the next run; malformed complete
records fail. Regenerate after the orchestrator finishes: this is a snapshot of a
growing session, not a claim that the session has ended.
