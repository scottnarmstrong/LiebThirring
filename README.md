# Stability of matter, formalized in Lean 4

[![Build and verify](https://github.com/scottnarmstrong/LiebThirring/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/scottnarmstrong/LiebThirring/actions/workflows/build.yml)
[![Comparators](https://github.com/scottnarmstrong/LiebThirring/actions/workflows/comparators.yml/badge.svg?branch=main)](https://github.com/scottnarmstrong/LiebThirring/actions/workflows/comparators.yml)

A **Lean 4 / Mathlib** formalization of non-relativistic Coulomb matter in three dimensions. The main results are:

- **Stability of matter.** The energy of fermionic electrons and static nuclei is bounded below by a constant times the total particle count, with both an extended-energy inequality and a real quadratic-form version.
- **Kinetic and electrostatic inequalities.** The kinetic Lieb–Thirring inequality with Rumin's explicit constant, and Baxter's electrostatic inequality including its positive nearest-other-nucleus correction.
- **Atomic ionization.** An atom of charge $`Z\gt 0`$ can have a weak ground state, or bind strictly against electron removal, only if $`N\lt 2Z+1`$.
- **The thermodynamic limit.** Neutral matter with quantum nuclei of one species has a unique continuous convex energy density at zero temperature, obtained along every sequence of Dirichlet balls with convergent particle density.
- **Thomas–Fermi theory.** The molecular electronic and total energies converge to the TF energy in the large-charge limit. The relaxed TF problem has a unique minimizer, with mass saturation and exact-mass attainment characterized by neutrality.

The stability constants depend only on the spin multiplicity and maximum nuclear charge, uniformly over nuclear positions.

## Results formalized

The following lists the results covered from each paper. The detailed formulations and Lean declarations appear below.


- **Elliott H. Lieb and Walter E. Thirring, “Bound for the kinetic energy of fermions which proves the stability of matter”, Physical Review Letters 35 (1975), 687–689** ([DOI](https://doi.org/10.1103/PhysRevLett.35.687)); **erratum, 35 (1975), 1116** ([DOI](https://doi.org/10.1103/PhysRevLett.35.1116)).

  - The three-dimensional kinetic inequality of equation (10), for normalized antisymmetric space-and-spin states, with arbitrary positive spin multiplicity and Rumin's coefficient $`K_{\mathrm R}q^{-2/3}`$. The numerical coefficient differs from the original paper; no sharp-constant claim is made.
  - The stability conclusion in equation (16) and its following remarks, presented here in the modern Solovej formulation for static nuclei and bounded nonnegative, possibly unequal charges: additive nonnegative extended-energy and real quadratic-form versions with an explicit constant.

- **J. R. Baxter, “Inequalities for potentials of particle systems”, Illinois Journal of Mathematics 24 (1980), 645–652** ([DOI](https://doi.org/10.1215/ijm/1256047480)).

  - Baxter's electrostatic inequality in the form of Lundholm's Theorem 7.2, equation (7.7), for equal nuclear charges: the inverse nearest-nucleus bound with its positive $`Z^2/4`$ nearest-other-nucleus correction. The extended-energy statement includes collisions and empty configurations; the proof uses nuclear Voronoi face measures.

- **Elliott H. Lieb, “Bound on the maximum negative ionization of atoms and molecules”, Physical Review A 29 (1984), 3018–3028** ([DOI](https://doi.org/10.1103/PhysRevA.29.3018)).

  - Theorem 1 in the atomic, nonrelativistic unit-electron-charge case: $`N\lt 2Z+1`$, equation (2.11), for normalized weak form-domain ground states and for strict binding against removal of one electron. Nuclear charge is any positive real number and spin multiplicity is any positive integer; there is no magnetic field.

- **Elliott H. Lieb and Joel L. Lebowitz, “The constitution of matter: Existence of thermodynamics for systems composed of electrons and nuclei”, Advances in Mathematics 9 (1972), 316–398** ([DOI](https://doi.org/10.1016/0001-8708(72)90023-0)).

  - The neutral thermodynamic-limit argument of Theorems 4.6 and 5.1, using the finite-packing constructions of Theorems 3.1–3.2, adapted to zero-temperature canonical ground energies. The resulting energy density is unique, continuous and convex, and the limit includes zero density.
  - The model has fermionic electrons with arbitrary positive finite spin multiplicity, spinless bosonic nuclei of one positive integer charge and finite positive mass, and Dirichlet confinement to balls. Theorem 8.1 gives the paper's broader entropy-dependent energy-density result; the result here concerns ground energies at zero temperature.

- **Elliott H. Lieb and Barry Simon, “The Thomas–Fermi theory of atoms, molecules and solids”, Advances in Mathematics 23 (1977), 22–116** ([DOI](https://doi.org/10.1016/0001-8708(77)90108-6)).

  - Theorem III.1, equation (45): the molecular large-charge energy limit, both electronic and total. Nuclear charges scale by $`\alpha`$, positions by $`\alpha^{-1/3}`$, and energies by $`\alpha^{-7/3}`$. The kinetic normalization is $`-\Delta`$ with arbitrary fixed positive spin multiplicity, and the TF mass is any $`\nu\gt 0`$, including above neutrality.
  - Theorem II.14, specialized to Coulomb nuclear potentials: existence and almost-everywhere uniqueness of the relaxed TF minimizer, allowing arbitrary positive kinetic coefficient, nonnegative charges and coincident nuclei.
  - The Coulomb-potential mass threshold of Theorems II.17–II.20 and the constancy above neutrality in Theorem II.32(ii): relaxed minimizer mass $`\min\{\nu,\sum_kz_k\}`$, saturation of the exact-mass infimum above neutrality, and exact-mass attainment precisely at or below neutrality, for positive charges at distinct positions.

- **Elliott H. Lieb, “Thomas–Fermi and related theories of atoms and molecules”, Reviews of Modern Physics 53 (1981), 603–641** ([DOI](https://doi.org/10.1103/RevModPhys.53.603)); **erratum, 54 (1982), 311** ([DOI](https://doi.org/10.1103/RevModPhys.54.311)).

  - Theorems 2.4–2.5 and 3.18: the corresponding relaxed minimization and neutral mass-saturation results, in the Coulomb model just described.
  - Theorem 5.1: the corresponding molecular TF energy limit, with the same spin and kinetic-unit conventions. The formalization uses Neumann and Dirichlet cubes and Slater trial states, following Lieb–Simon; the review presents a coherent-state alternative.

## Sources

The proofs also use the following surveys, lecture notes and papers. The entries identify proof methods and background; their full collections of results are outside the scope listed above.

- Rupert L. Frank, *The Lieb–Thirring inequalities: Recent results and open problems* (2020), **Corollary 6, Theorem 7 and Lemma 8** ([arXiv:2007.09326](https://arxiv.org/abs/2007.09326)). Solovej's stability argument and its kinetic and electrostatic inputs.
- Douglas Lundholm, *Methods of Modern Mathematical Physics: Uncertainty and Exclusion Principles in Quantum Mechanics*, lecture notes, revision July 27, 2019, **Theorem 6.1, Corollary 6.8, Theorem 7.2 and Theorem 7.6** ([author's notes](https://www.math.lmu.de/~lundholm/methmmp.pdf); related [arXiv:1805.03063](https://arxiv.org/abs/1805.03063)). The kinetic inequality with spin, the Voronoi proof of Baxter and the stability argument.
- Michel Rumin, *Balanced distribution-energy inequalities and related entropy bounds*, Duke Mathematical Journal **160** (2011), 567–597, **Sections 3.1–3.3 of the preprint** ([arXiv:1008.1674](https://arxiv.org/abs/1008.1674); [DOI](https://doi.org/10.1215/00127094-1444305)). The distribution-energy method underlying the direct kinetic estimate.
- Rupert L. Frank, Dirk Hundertmark, Michal Jex and Phan Thành Nam, *The Lieb–Thirring inequality revisited*, Journal of the European Mathematical Society **23** (2021), 2583–2600 ([arXiv:1808.09017](https://arxiv.org/abs/1808.09017); [DOI](https://doi.org/10.4171/JEMS/1062)). Rumin's argument and kinetic constants.
- Jan Philip Solovej, *Many Body Quantum Mechanics*, lecture notes, March 5, 2014 ([author's notes](https://web.math.ku.dk/~solovej/MANYBODY/mbnotes-ptn-5-3-14.pdf)). Many-body, quadratic-form and second-quantization background.
- Phan Thành Nam, *New bounds on the maximum ionization of atoms*, Communications in Mathematical Physics **312** (2012), 427–445, **Section 2.1** ([arXiv:1009.2367](https://arxiv.org/abs/1009.2367); [DOI](https://doi.org/10.1007/s00220-012-1479-y)). An exposition of Lieb's weighted atomic argument.
- Søren Fournais, Mathieu Lewin and Jan Philip Solovej, *The semi-classical limit of large fermionic systems*, Calculus of Variations and Partial Differential Equations **57** (2018), article 105, **Section 3** ([arXiv:1510.01124](https://arxiv.org/abs/1510.01124); [DOI](https://doi.org/10.1007/s00526-018-1374-2)). Semiclassical energy comparisons and cube trial states.
- Phan Thành Nam, *Functional Analysis II*, lecture notes, Winter 2020–2021, **Chapter 8** ([author's notes](https://www.math.lmu.de/~nam/LectureNotesFA2021.pdf)). TF energy limits and cube Slater trials.
- Phan Thành Nam, *Mathematical Quantum Mechanics II*, lecture notes, Summer 2020, **Sections 1.4 and 4.3** ([author's notes](https://www.math.lmu.de/~nam/LectureNotesMQM2020.pdf)). Many-body and determinant background, and a regular-kernel Onsager lemma.
- Michael Loss, *Thomas-Fermi theory*, Quantum Coulomb Systems lecture chapter (2005) ([course notes](https://loss.math.gatech.edu/MUNICH/QUANTUMCOULOMB/PDFFILES/10thomasfermi.pdf)). TF minimization and the neutral mass threshold.
- Elliott H. Lieb and Walter E. Thirring, *Inequalities for the moments of the eigenvalues of the Schrödinger Hamiltonian and their relation to Sobolev inequalities*, in *Studies in Mathematical Physics: Essays in Honor of Valentine Bargmann* (1976), 269–303 ([DOI](https://doi.org/10.1515/9781400868940-014)). The original eigenvalue-moment and duality treatment; the formalized kinetic inequality is the three-dimensional version stated above.

The stability proofs follow the cited Frank, Lundholm and Rumin versions. The original Lieb–Thirring, Baxter, Lieb, Lieb–Lebowitz and Lieb–Simon papers, and the listed errata, were also available in full. The source relationships and adaptations are recorded in [`formalization.yaml`](formalization.yaml).

## Fixed-nucleus states and energies

There are $`N\ge0`$ electrons, each with $`q\ge1`$ spin states, and $`M\ge0`$ static nuclei at positions $`R_k\in\mathbb R^3`$. Nuclear charges satisfy $`0\le z_k\le Z`$. A state is

```math
\psi\in L^2\bigl((\mathbb R^3)^N;\mathbb C^{\{1,\ldots,q\}^N}\bigr),\qquad \|\psi\|_2=1.
```

Antisymmetry means that simultaneously permuting spatial and spin coordinates multiplies the state by the sign of the permutation, almost everywhere. The norm $`|\psi(x)|^2`$ sums over all spin labels. The one-particle spatial density is

```math
\rho_\psi(y)=\sum_{i=1}^N\int_{(\mathbb R^3)^{N-1}}|\psi(x_1,\ldots,x_{i-1},y,x_{i+1},\ldots,x_N)|^2\,dx_{\widehat i},\qquad \int_{\mathbb R^3}\rho_\psi=N.
```

The Fourier transform uses the phase $`e^{-2\pi i x\cdot\xi}`$, extended unitarily to $`L^2`$. The kinetic energy is the nonnegative extended quadratic form

```math
T[\psi]=\int_{\mathbb R^{3N}}(2\pi)^2|\xi|^2|\widehat\psi(\xi)|^2\,d\xi\in[0,\infty].
```

Thus the electron kinetic operator is $`\sum_i-\Delta_{x_i}`$. The fixed-nucleus model has no nuclear kinetic term; the thermodynamic model below gives nuclei their own quantum kinetic energy. There is no magnetic field. Write the electron–nucleus attraction, electron repulsion and nuclear repulsion as

```math
A_z(x,R)=\sum_{i,k}\frac{z_k}{|x_i-R_k|},\qquad B(x)=\sum_{i\lt j}\frac1{|x_i-x_j|},\qquad U_z(R)=\sum_{k\lt l}\frac{z_kz_l}{|R_k-R_l|}.
```

Their state expectations are $`\langle A_z\rangle_\psi=\int A_z(x,R)|\psi(x)|^2\,dx`$ and $`\langle B\rangle_\psi=\int B(x)|\psi(x)|^2\,dx`$. All integrals in these definitions are nonnegative lower integrals, valued in $`[0,\infty]`$ (`ℝ≥0∞` in Lean). The Coulomb kernel is $`\infty`$ at a collision; extended multiplication has $`0\cdot\infty=0`$, so a zero charge contributes zero even there. Empty sums are zero. A nearest distance over an empty set is $`\infty`$, with inverse zero.

The definitions are in [`LiebThirring/Defs/`](LiebThirring/Defs/):

| Module | Lean definitions (namespace `LiebThirring`) |
| --- | --- |
| [Configuration](LiebThirring/Defs/Configuration.lean) | `Position`, `Configuration`, `SpinLabels`, `SpinAmplitudes`, `State`, `particlePosition`, `permutePositions`, `permuteSpins`, `OtherConfiguration`, `insertParticle` |
| [Antisymmetric](LiebThirring/Defs/Antisymmetric.lean) | `antisymmetric` |
| [Density](LiebThirring/Defs/Density.lean) | `density` |
| [KineticEnergy](LiebThirring/Defs/KineticEnergy.lean) | `kineticEnergy` |
| [Coulomb](LiebThirring/Defs/Coulomb.lean) | `coulombKernel`, `electronRepulsion`, `attraction`, `nuclearRepulsion`, `nearestNucleusDistance`, `nearestOtherNucleusDistance`, `nearestNucleusControl`, `baxterCorrection` |
| [RuminConstant](LiebThirring/Defs/RuminConstant.lean) | `ruminConstant` |

## Stability inequalities

**Stability of matter.** For every $`q\ge1`$ and $`Z\ge0`$ there is $`C(q,Z)\gt 0`$ such that, for every $`N,M`$, every choice of charges $`0\le z_k\le Z`$, every nuclear configuration and every normalized antisymmetric $`L^2`$ state,

```math
\langle A_z\rangle_\psi\le T[\psi]+\langle B\rangle_\psi+U_z(R)+C(q,Z)(N+M).
```

Lean: [`LiebThirring.stability_of_matter`](LiebThirring/Theorems/StabilityOfMatter.lean). This additive inequality in $`[0,\infty]`$ includes infinite kinetic energy and coincident nuclei. When the energies are finite, rearranging it gives the quadratic-form bound $`H\ge-C(q,Z)(N+M)`$ for $`H=\sum_i-\Delta_{x_i}+B+U_z-A_z`$. The additive formulation states the estimate without subtracting infinite quantities.

**Real quadratic-form stability.** With the same parameter dependence, for pairwise distinct nuclear positions and a normalized antisymmetric state with $`T[\psi]\lt \infty`$, the three quantities $`\langle A_z\rangle_\psi`$, $`\langle B\rangle_\psi`$ and $`U_z(R)`$ are finite and

```math
T[\psi]+\langle B\rangle_\psi+U_z(R)-\langle A_z\rangle_\psi\ge-C(q,Z)(N+M).
```

Lean: [`LiebThirring.stability_of_matter_real`](LiebThirring/Theorems/StabilityOfMatterReal.lean). Finiteness is part of the conclusion, so the conversions from extended nonnegative values to real numbers (`ENNReal.toReal`) are valid. Hardy's inequality supplies the Coulomb integrability needed for this form bound.

**Kinetic Lieb–Thirring inequality.** For every $`q\ge1`$, every $`N\ge0`$, and every normalized antisymmetric $`L^2`$ state,

```math
K_{\mathrm R}\,q^{-2/3}\int_{\mathbb R^3}\rho_\psi(y)^{5/3}\,dy\le T[\psi],\qquad K_{\mathrm R}=\frac9{35}(6\pi^2)^{2/3}.
```

Lean: [`LiebThirring.kinetic_lieb_thirring`](LiebThirring/Theorems/KineticLiebThirring.lean). The constant is `LiebThirring.ruminConstant`; it is the explicit coefficient from Rumin's argument. The inequality is in $`[0,\infty]`$ and requires no finite-energy hypothesis.

**Baxter's electrostatic inequality.** For every $`N,M\ge0`$, $`Z\ge0`$ and every spatial configuration, let $`d_i=\min_k|x_i-R_k|`$ and $`D_k=\min_{l\ne k}|R_k-R_l|`$. For equal nuclear charges $`Z`$,

```math
A_Z(x,R)+\frac{Z^2}{4}\sum_{k=1}^M D_k^{-1}\le B(x)+U_Z(R)+(2Z+1)\sum_{i=1}^N d_i^{-1}.
```

Lean: [`LiebThirring.baxter`](LiebThirring/Theorems/Baxter.lean). This includes the positive nearest-other-nucleus correction and holds in $`[0,\infty]`$, including collisions and empty configurations. The assembly of stability also proves the weaker bound needed for unequal charges $`z_k\le Z`$.

**Classical meaning of the kinetic energy.** For every $`N,q\ge0`$ and every spin-valued Schwartz function $`f`$ on $`\mathbb R^{3N}`$,

```math
T[f]=\sum_{i=1}^N\sum_{a=1}^3\int_{\mathbb R^{3N}}|\partial_{x_{i,a}}f(x)|^2\,dx.
```

Lean: [`LiebThirring.kineticEnergy_schwartz`](LiebThirring/Theorems/KineticEnergySchwartz.lean), applied to the $`L^2`$ state represented by $`f`$. This identifies the Fourier definition with the classical Dirichlet integral, including its normalization.

The stability proof chooses an explicit constant. Set $`\kappa=K_{\mathrm R}q^{-2/3}`$ and $`b=\frac25(\frac35)^{3/2}`$. One choice, also used for the real form, is

```math
C(q,Z)=\max\{1,8\pi b\}\frac{(2Z+1)^2}{\kappa}\gt 0.
```

This constant is independent of $`N,M,z,R,\psi`$; no optimality is claimed. The chosen nearest-nucleus cutoff radius is $`\kappa/(2Z+1)`$.

## Atomic ionization

For one static nucleus of real charge $`Z\gt 0`$ at the origin and $`q\ge1`$ electron spin states, write $`E_q(N,Z)`$ for the infimum of $`T+\langle B\rangle-\langle A_Z\rangle`$ over normalized antisymmetric states with finite kinetic energy. This is [`LiebThirring.atomicGroundStateEnergy`](LiebThirring/Ionization/AtomicGroundStateEnergy.lean), defined in the extended real line (`EReal`) using [`FormDomain`](LiebThirring/Variational/FormDomain.lean) and [`groundStateEnergy`](LiebThirring/Variational/GroundStateEnergy.lean). Nuclear charge need not be an integer, and the kinetic normalization is $`-\Delta`$.

A weak ground state is a unit vector $`\psi`$ in the form domain whose real energy equals this variational infimum and which satisfies

```math
h_{N,Z}(\varphi,\psi)=E_q(N,Z)\langle\varphi,\psi\rangle
```

for every form-domain test state $`\varphi`$. The sesquilinear form and predicate are [`LiebThirring.energyForm`](LiebThirring/Variational/EnergyForm.lean) and [`LiebThirring.is_weak_ground_state`](LiebThirring/Variational/WeakGroundState.lean).

**Ground-state and binding bounds.** For every $`N\ge0`$, a weak atomic ground state implies $`N\lt 2Z+1`$. Strict binding gives the same conclusion:

```math
E_q(N,Z)\lt E_q(\max\{N-1,0\},Z)\quad\Longrightarrow\quad N\lt 2Z+1.
```

Lean: [`LiebThirring.electron_count_lt_of_atomic_weak_ground_state`](LiebThirring/Ionization/WeakGroundStateBound.lean) and [`LiebThirring.electron_count_lt_of_atomic_binding`](LiebThirring/Ionization/BindingBound.lean). Binding is the strict `EReal` inequality displayed above. The weak-state version also applies when the ground energy equals the electron-removal threshold; it assumes attainment rather than strict binding.

The proof tests the weak equation with bounded approximations of radial distance multipliers. Positivity of the weighted kinetic form and the pair-distance inequality $`|x_i|+|x_j|\ge|x_i-x_j|`$ give the strict electron-count bound. For the binding version, localization separates escaping electrons, and compactness below the removal threshold produces a weak ground state. This is the atomic unit-charge specialization of **Lieb (1984), Theorem 1, equations (2.9), (2.11) and (4.1)–(4.5)**; the bound is independent of spin multiplicity.

## Thermodynamic limit

Here the nuclei move quantum mechanically. Fix $`q\ge1`$, an integer nuclear charge $`z\ge1`$, and a finite nuclear mass $`m\gt 0`$ in electron-mass units. Electrons are antisymmetric with $`q`$ spin states; nuclei are spinless bosons. The Hamiltonian is

```math
H_{N,M}=-\sum_{i=1}^N\Delta_{x_i}-\frac1m\sum_{k=1}^M\Delta_{y_k}
+\sum_{i\lt j}\frac1{|x_i-x_j|}
+z^2\sum_{k\lt l}\frac1{|y_k-y_l|}
-z\sum_{i,k}\frac1{|x_i-y_k|}.
```

All particle positions lie in the ball $`B_L\subset\mathbb R^3`$, with Dirichlet boundary conditions defined by closure of smooth compactly supported states in the full kinetic form norm. Let $`E^D_{q,z,m}(N,M;L)`$ be the normalized variational infimum. The joint state, statistics, form domain, confinement and energy are defined in [`LiebThirring/Thermodynamic/`](LiebThirring/Thermodynamic/), notably `QuantumState`, `quantum_antisymmetric`, `nuclear_symmetric`, `QuantumFormDomain`, `is_dirichlet_ball`, `DirichletBallFormDomain`, `quantumEnergy`, `nuclearKineticCoefficient` ($`m^{-1}`$), and `confinedGroundStateEnergy`. The infimum takes values in `EReal`.

**Neutral energy density.** There is a unique continuous convex function $`e_{q,z,m}:[0,\infty)\to\mathbb R`$, with $`e_{q,z,m}(0)=0`$, such that for every $`\rho\ge0`$ and every sequence of positive radii and integer nuclear counts,

```math
L_j\longrightarrow\infty,\qquad
\frac{M_j}{|B_{L_j}|}\longrightarrow\rho
\quad\Longrightarrow\quad
\frac{E^D_{q,z,m}(zM_j,M_j;L_j)}{|B_{L_j}|}\longrightarrow e_{q,z,m}(\rho).
```

Lean: [`LiebThirring.exists_unique_thermodynamic_energy_density`](LiebThirring/Thermodynamic/ThermodynamicLimit.lean). The parameter $`\rho`$ is **nuclear density**; electron density is $`z\rho`$. Neutrality is exact at every index, $`N_j=zM_j`$, and [`LiebThirring.ballVolume`](LiebThirring/Thermodynamic/BallVolume.lean) is $`4\pi L^3/3`$. Convergence is in the extended real line to the finite value $`e_{q,z,m}(\rho)`$, including $`\rho=0`$; no growth condition on $`M_j`$ is imposed beyond the density limit.

The proof assembles neutral trial clusters with the two species' statistics. Independent rotations and Newton's theorem eliminate the averaged intercluster Coulomb interaction. Finite ball packings and balanced integer rounding give energy comparisons; a renewal argument yields convergence along a fixed geometric sequence. Convexity gives density continuity, and inner and complementary packings transfer convergence to arbitrary radii and counts. Stability and dilute trials treat zero density. This adapts the screening, packing and renewal arguments of **Lieb–Lebowitz (1972), Theorems 3.1–3.2, 4.6 and 5.1**, to zero-temperature canonical energies; their **Theorem 8.1** treats energy-density limits in a broader entropy-dependent setting. The result here concerns Dirichlet balls and one nuclear species.

## Thomas–Fermi theory

Thomas–Fermi densities are nonnegative almost-everywhere classes in $`L^1(\mathbb R^3)\cap L^{5/3}(\mathbb R^3)`$, with no quantum representability condition. For $`a\gt 0`$, nonnegative charges $`z_k`$ and positions $`R_k`$, define the electronic functional and its exact-mass and relaxed infima by

```math
\begin{aligned}
\mathcal F_a[\rho;z,R]&=
a\int\rho^{5/3}-\int\left(\sum_k\frac{z_k}{|x-R_k|}\right)\rho(x)\,dx
+\frac12\iint\frac{\rho(x)\rho(y)}{|x-y|}\,dx\,dy,\\
e_a(\nu;z,R)&=\inf_{\rho\ge0,\ \int\rho=\nu}\mathcal F_a[\rho;z,R],
\qquad e_a^{\le}(\nu;z,R)=\inf_{\rho\ge0,\ \int\rho\le\nu}\mathcal F_a[\rho;z,R].
\end{aligned}
```

The definitions in [`LiebThirring/ThomasFermi/`](LiebThirring/ThomasFermi/) are `TFDensity`, `tfMass`, `tfDensityMeasure`, `tfNuclearPotential`, `tfCoulombEnergy` (including the factor $`1/2`$), `tfFunctional`, `tfEnergy` and `tfRelaxedEnergy`. Both infima are defined in `EReal`; `tfFunctional` is the electronic energy and omits the nuclear constant $`U_z(R)`$.

**Molecular large-charge limit.** Fix $`q\ge1`$, $`\nu\gt 0`$, at least one nucleus, positive real charges $`z_k`$ and pairwise distinct positions $`R_k`$. For every sequence of natural numbers $`N_j\to\infty`$, put $`\alpha_j=N_j/\nu`$. With the $`-\Delta`$ kinetic normalization,

```math
K_q=\frac35\left(\frac{6\pi^2}{q}\right)^{2/3},\qquad
\alpha_j^{-7/3}E_q^{\mathrm{el}}(N_j;\alpha_j z,\alpha_j^{-1/3}R)
\longrightarrow e_{K_q}(\nu;z,R).
```

Lean: [`LiebThirring.tendsto_electronicGroundStateEnergy_tf`](LiebThirring/ThomasFermi/MolecularLimit.lean), using `LiebThirring.electronicGroundStateEnergy` and `LiebThirring.tfKineticConstant`. Thus $`N_j=\alpha_j\nu`$ exactly; the charge scale is $`\alpha_j`$, the length scale is $`\alpha_j^{-1/3}`$ and the energy scale is $`\alpha_j^{7/3}`$. Here $`\nu`$ is the TF mass, equivalently the scaled electron count; $`m`$ in the thermodynamic model is the nuclear-to-electron mass ratio.

The total-energy version includes nuclear repulsion on both sides:

```math
\alpha_j^{-7/3}E_q(N_j;\alpha_j z,\alpha_j^{-1/3}R)
\longrightarrow e_{K_q}(\nu;z,R)+U_z(R).
```

Lean: [`LiebThirring.tendsto_groundStateEnergy_tf`](LiebThirring/ThomasFermi/TotalLimit.lean), using `LiebThirring.groundStateEnergy`. This version also requires the scaled positions to be pairwise distinct at every index; injectivity of $`R`$ ensures this at indices with $`N_j\gt 0`$. Both limits hold for every $`\nu\gt 0`$, including $`\nu\gt \sum_kz_k`$, without an eigenfunction or minimizer assumption. They adapt **Lieb–Simon (1977), Theorem III.1, equation (45)**, and **Lieb (1981), Theorem 5.1**, to fixed arbitrary spin multiplicity and the stated kinetic units.

The lower bound uses Neumann cubes: antisymmetry bounds mode occupations, sharp filled-mode sums give the semiclassical kinetic coefficient, and boxwise Coulomb comparison retains the direct density interaction. A small fraction of kinetic energy pays for the nuclear cores. The upper bound fills Dirichlet modes in Slater determinants approximating compact step densities; distant orbitals correct the electron count at negligible scaled cost. Dilation and ordered removal of the core and mesh cutoffs give the two limits.

**Minimizers and neutrality.** For every $`a\gt 0`$, $`\nu\ge0`$ and finite nonnegative nuclear data, even with coincident positions, the relaxed problem has a unique minimizer, with uniqueness understood almost everywhere. Lean: [`LiebThirring.exists_unique_tfRelaxedMinimizer`](LiebThirring/ThomasFermi/RelaxedMinimizer.lean). If the charges are positive and positions are pairwise distinct, put $`Z_0=\sum_kz_k`$. Then

```math
e_a(\nu;z,R)=e_a(\min\{\nu,Z_0\};z,R),\qquad
e_a(\nu;z,R)\text{ is attained at exact mass }\nu\ \Longleftrightarrow\ \nu\le Z_0.
```

Every relaxed minimizer has mass $`\min\{\nu,Z_0\}`$. Lean: [`LiebThirring.tfEnergy_saturation_and_attainment`](LiebThirring/ThomasFermi/Saturation.lean). Excess mass can escape to infinity without changing the infimum, so equality of energies above neutrality does not imply exact-mass attainment.

Quantitative convexity makes a relaxed minimizing sequence Cauchy in $`L^{5/3}`$; completeness, mass closure and Coulomb continuity give its minimizer, and strict convexity gives uniqueness. For positive mass caps, first variations yield the screened-potential equation. Positivity, spherical averaging and a maximum-principle argument identify the neutral mass threshold. These results correspond to **Lieb–Simon, Theorems II.14, II.17–II.20 and II.32**, and **Lieb (1981), Theorems 2.4–2.5 and 3.18**.

## Stability proof

The kinetic estimate begins with the Pauli occupation bound: the sum of the lifted rank-one projections onto a normalized one-particle spatial-and-spin orbital has expectation at most one in a normalized antisymmetric state. Applied to low-momentum test functions and summed over spin, this bounds the low-momentum density. Rumin's layer-cake representation expresses kinetic energy as the integral of the high-momentum mass. The triangle inequality between low- and high-momentum parts, followed by integration over the energy threshold, yields the $`\rho^{5/3}`$ bound with $`K_{\mathrm R}`$.

Baxter's inequality is proved using charge distributed on the faces of the nuclear Voronoi cells. A divergence theorem obtained by slicing along lines identifies the distributional Laplacian of the screened potential with this face measure. The Coulomb fundamental solution and the maximum principle identify its potential. Newton's theorem controls spherical shell charges, and positivity of Coulomb energy permits square completion. The energy deficit gives the $`Z^2/4`$ correction. Separate collision and empty-configuration arguments extend the result to all configurations.

The stability proof integrates the electrostatic bound against the state, handles unequal charges by finite averaging, and splits the inverse nearest-nucleus distance at radius $`\kappa/(2Z+1)`$. Outside that radius, the density mass gives a cost proportional to $`N`$. Inside it, Young's inequality and the kinetic estimate reduce the cost to a $`5/2`$-power integral of the cutoff, bounded by the sum of $`M`$ radial one-center integrals. Hardy's inequality, applied to one-particle slices and electron pairs, proves finiteness of the Coulomb expectations for the real form.

The stability argument follows **Solovej's proof**, as presented in Frank's survey, Corollary 6 and Theorem 7, and Lundholm's lecture notes, Theorem 7.6. The kinetic argument follows Rumin, with the orthonormal and spin versions presented in Lundholm's Theorem 6.1 and Corollary 6.8; the electrostatic proof follows Lundholm's Theorem 7.2. The formulation here uses the kinetic normalization $`-\Delta`$, bounded unequal nuclear charges, and nonnegative extended energies. It proves the kinetic inequality in dimension three, rather than the general eigenvalue-moment family.

## Build and verify

Install [Lean's elan toolchain manager](https://github.com/leanprover/elan). From a fresh checkout, run:

```sh
lake exe cache get
lake build
```

The toolchain is **`leanprover/lean4:v4.35.0-rc2`**. Mathlib is **`v4.35.0-rc2`**, resolved in `lake-manifest.json` to **`065356127b1dc0016f66b7283ce0ce2c4055aa55`**. The manifest pins all dependencies.

Check the axiom dependencies of all twelve main theorems listed above and the module requirements:

```sh
python3 -I .github/scripts/check_axioms.py
python3 -I scripts/check_lean_modules.py --root .
```

The axiom script runs `#print axioms` for each named theorem, requires all twelve reports, and rejects every axiom outside `propext`, `Classical.choice` and `Quot.sound`.

The [Mathlib-only challenge](LiebThirringAudit/Challenge/StabilityOfMatter.lean) and its [solution](LiebThirringAudit/Solution/StabilityOfMatter.lean), selected by [`comparator.json`](comparator.json), compare nine results: extended and real-form stability, kinetic Lieb–Thirring, Baxter, both atomic ionization bounds, the thermodynamic limit, and both molecular Thomas–Fermi limits. The challenge states the definitions independently and contains nine intentional theorem placeholders; the solution supplies proofs from the library. The Schwartz identity is covered by the build and axiom check.

Install the sandbox executable [landrun](https://github.com/zouuup/landrun) and the independent checker [NanoDa](https://github.com/robsimmons/nanoda_lib), making `landrun` and `nanoda_bin` available on `PATH`, then run:

```sh
scripts/verify_comparator.sh
```

The script fetches and builds the pinned `leanprover/comparator` and `leanprover/lean4export`. It checks statement and definition dependency correspondence, permitted axioms, and independent NanoDa proof replay. `COMPARATOR_LANDRUN` and `COMPARATOR_NANODA` may specify the executable paths. Continuous integration runs on every push: the [build workflow](.github/workflows/build.yml) performs the build, axiom, module and metadata checks, and the [comparator workflow](.github/workflows/comparators.yml) sets up the tools and runs the comparator and NanoDa checks. The [local metadata checker](scripts/check_palomar.py) reports preparation checks only; a [Palomar submission](https://submit.palomar-registry.org/) performs its own verification and review.

## Library map

Each extension theorem statement has its own short file; its proof is assembled in
[`LiebThirring/Proofs/`](LiebThirring/Proofs/).

| Directory | Content |
| --- | --- |
| [`LiebThirring/Defs`](LiebThirring/Defs/) | States, density, kinetic form, Coulomb interactions and Rumin's constant |
| [`LiebThirring/Theorems`](LiebThirring/Theorems/) | Stability, kinetic and electrostatic results |
| [`LiebThirring/Kinetic`](LiebThirring/Kinetic/) | Pauli projections, momentum cutoffs and Rumin's layer cake |
| [`LiebThirring/Electrostatics`](LiebThirring/Electrostatics/) | Voronoi face measure, slicing divergence theorem, Newton's theorem and Coulomb positivity |
| [`LiebThirring/Analysis`](LiebThirring/Analysis/) | Coulomb fundamental solution, weak harmonic functions, maximum principle and Hardy's inequality |
| [`LiebThirring/Fourier`](LiebThirring/Fourier/) | Fourier identities, tensor products and the Schwartz kinetic identity |
| [`LiebThirring/Assembly`](LiebThirring/Assembly/) | Unequal-charge averaging, nearest-nucleus cutoff and extended and real-form stability |
| [`LiebThirring/Variational`](LiebThirring/Variational/) | Antisymmetric form domain, real and sesquilinear Coulomb forms, weak eigenfunctions and variational ground energies |
| [`LiebThirring/Ionization`](LiebThirring/Ionization/) | Atomic ionization bounds, weighted kinetic estimates, localization, compactness and binding-to-ground-state existence |
| [`LiebThirring/Thermodynamic`](LiebThirring/Thermodynamic/) | Quantum nuclear model, Dirichlet ball energies, stability and the thermodynamic limit |
| [`ThermoClusters`](LiebThirring/ThermoClusters/), [`ThermoNeutral`](LiebThirring/ThermoNeutral/), [`Packing`](LiebThirring/Packing/), [`ThermoLimit`](LiebThirring/ThermoLimit/) | Neutral cluster assembly and screening, finite packings, integer interpolation, renewal convergence and density continuity |
| [`LiebThirring/ThomasFermi`](LiebThirring/ThomasFermi/) | TF densities, electronic functional, exact and relaxed infima, molecular limits and minimizer theorems |
| [`TFQuantum`](LiebThirring/TFQuantum/), [`TFCubes`](LiebThirring/TFCubes/), [`TFProduct`](LiebThirring/TFProduct/), [`TFLattice`](LiebThirring/TFLattice/), [`TFSectors`](LiebThirring/TFSectors/) | Dilation, Slater states, cube spectral theory, sharp mode sums and fermionic sector bounds |
| [`TFCore`](LiebThirring/TFCore/), [`TFCoulomb`](LiebThirring/TFCoulomb/), [`TFUpper`](LiebThirring/TFUpper/), [`TFLimit`](LiebThirring/TFLimit/) | Nuclear-core estimates, boxwise Coulomb comparison, Dirichlet trials and molecular limit assembly |
| [`TFFunctional`](LiebThirring/TFFunctional/), [`TFMinimizer`](LiebThirring/TFMinimizer/) | TF continuity and mass completion, quantitative convexity, minimizer existence, screened potentials and neutrality |

## How this was built

The Lean code was written with AI coding agents under the authors' supervision. The authors approved every exact Lean definition and theorem statement, and Lean checks the proofs against those statements. The models and tools are recorded in [`formalization.yaml`](formalization.yaml). The redacted session transcript is in [`transcript/`](transcript/).

## Authors and citation

The Lean development is by

- **Scott Armstrong** — CNRS and Laboratoire Jacques-Louis Lions, Sorbonne Université; Courant Institute School of Mathematics, Computing, and Data Science, New York University
- **Amélie Loher** — All Souls College, University of Oxford

If you use this formalization, please cite it using the metadata in [`CITATION.cff`](CITATION.cff).

## Acknowledgements

Scott Armstrong was supported by the European Research Council (ERC) under the European Union's Horizon Europe research and innovation programme, grant agreement No. 101200828.
Amélie Loher acknowledges support from the Fondation Sciences Mathématiques de Paris.

## License

The Lean code in this repository is licensed under the **Apache License 2.0** (see [`LICENSE`](LICENSE)).
