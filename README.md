# Poincare: the Poincare conjecture in HOL Light

A complete formalization in [HOL Light](https://github.com/jrh13/hol-light) of the Poincare conjecture, following
Perelman's proof as presented in

> J. Morgan and G. Tian, *Ricci Flow and the Poincare Conjecture*, Clay Mathematics Monographs 3, American
> Mathematical Society and Clay Mathematics Institute, 2007,

together with Moise's theorem that every topological 3-manifold has a smooth structure, after

> E. E. Moise, *Geometric Topology in Dimensions 2 and 3*, Graduate Texts in Mathematics 47, Springer, 1977,

for the classical topological form. Every closed, simply connected 3-manifold is homeomorphic to the 3-sphere,
and every closed, simply connected smooth 3-manifold is diffeomorphic to it.

## Main theorems

Each theorem below is proved with no hypotheses, using only HOL Light's three standard axioms (`ETA_AX`,
`SELECT_AX`, `INFINITY_AX`). The development contains no unproved steps.

| theorem | statement | file |
|---|---|---|
| `POINCARE_TOP : \|- POINCARE_STATEMENT (:A)` | the Poincare conjecture: every compact, Hausdorff, nonempty, simply connected topological space that is locally Euclidean of dimension 3 is homeomorphic to the unit sphere of R^4 | `src/pc_poincare_top.ml` |
| `POINCARE_SMOOTH : \|- POINCARE_SMOOTH_STATEMENT (:A)` | the smooth form: every compact, Hausdorff, nonempty, simply connected smooth 3-manifold admits a smooth immersion into R^4 that is a homeomorphism onto the unit sphere, that is, it is diffeomorphic to the standard 3-sphere | `src/pc_smt_smooth.ml` |
| `POINCARE_EMBEDDED : \|- POINCARE_EMBEDDED_STATEMENT (:N)` | the topological form for subsets of R^N, in the library's own notions: every compact, nonempty, simply connected subset of R^N that is locally homeomorphic to R^3 is homeomorphic to the unit sphere of R^4 | `src/pc_poincare_top.ml` |
| `MOI_SST_HEADLINE : \|- !u:A->bool. MOISE_SMOOTHING_STATEMENT u` | Moise's theorem in the compact case: every compact Hausdorff space that is locally Euclidean of dimension 3 has a smooth atlas compatible with its topology | `src/pc_moi_status.ml` |

The argument `(:A)` of a statement constant only fixes the carrier type. Each theorem is proved for a type
variable, so it holds for every type. `POINCARE_TOP` is `POINCARE_FROM_SMOOTH_AND_MOISE` (`src/pc_interfaces.ml`)
applied to `POINCARE_SMOOTH` and `MOI_SST_HEADLINE`.

## What has to be trusted

- **HOL Light's kernel and its three axioms.**
- **The statements.** Only these files need to be read to know what has been proved; everything else is proof:
  - `src/poincare_statement.ml`: the three Poincare statements and the six definitions they use
    (`locally_euclidean_space`, `simply_connected_space`, `smooth_manifold_atlas`, `smooth_immersion_into`,
    `smooth_map_on`, `continuously_differentiable`), about 130 lines;
  - `src/pc_interfaces.ml`: `MOISE_SMOOTHING_STATEMENT`, if Moise's theorem is of interest.

  HOL Light itself computed the definitional dependencies of the statement constants. Beyond HOL Light's library
  (topological spaces, homeomorphisms, paths and homotopies, derivatives), `POINCARE_STATEMENT` depends on 2
  definitions of the development (`locally_euclidean_space`, `simply_connected_space`),
  `POINCARE_SMOOTH_STATEMENT` on 5, and `POINCARE_EMBEDDED_STATEMENT` on none: it is written entirely in the
  library's notions for sets in R^N (`compact`, `simply_connected`, `homeomorphic`, `sphere`).
- **An audit of the statements** is in `audit/`. It contains:
  - a formalization of both forms of the conjecture written independently from the texts of Morgan-Tian and of
    Milnor's Clay problem description, proved equivalent to ours and hence proved;
  - 30 sanity theorems testing the definitions: for instance, the 3-sphere satisfies all hypotheses, the circle
    is not simply connected, the 2-sphere is not locally Euclidean of dimension 3, the closed 3-ball (a manifold
    with boundary) satisfies every hypothesis except local Euclideanity, and the empty space shows that
    nonemptiness is needed.

  `doc/REPORT.md` compares the statements with the sources and with the two Lean formalizations, clause by
  clause. The Hausdorff hypothesis cannot be dropped either: the 3-sphere with one point doubled is compact,
  locally Euclidean and simply connected, but not Hausdorff (a standard example, not formalized here).

## Building

The development needs a built HOL Light. The commits of HOL Light that check this proof are tracked at
<https://hol-light.github.io/benchmark-results/>. Start HOL Light in the root directory of this repository. HOL Light's load path is first the current directory and then the HOL Light
directory, so `src/...` is found here and `Multivariate/...` in HOL Light. Then:

```
loadt "make.ml";;      (* load the development *)
loadt "check.ml";;     (* load it and print the headline theorems, their hypotheses and the axioms *)
```

To run non-interactively from the shell (in the repository root):

```
echo 'loadt "check.ml";;' | LINE_EDITOR=env /path/to/hol-light/hol.sh
```

`make.ml` first sets OCaml's garbage collector to keep the heap closer to the live data (`space_overhead` 40
instead of 120: a quarter less memory, half a percent more time), then loads HOL Light's `Multivariate/cauchy.ml`,
`Multivariate/lpspaces.ml` and `100/green.ml`, then the files of `src/` in dependency order. Every file also loads
its own prerequisites with `needs`, so once those three library files are loaded, any file of `src/` can be
loaded on its own.

Measured (CPU time) in a fresh session of the standard bytecode toplevel (one core),
peak memory about 17.5 GiB, on a shared machine with several such sessions running at the same time:

| stage | time |
|---|---|
| HOL Light core | 1.1 min |
| Multivariate up to `cauchy.ml`, `lpspaces.ml`, `100/green.ml` | 27.0 min |
| the development (`src/`) | 390.2 min (6.5 h) |
| **total** | **418.3 min (7.0 h)** |

`doc/timing.tsv` gives the time for each file. The audit (`loadt "audit/check.ml";;`) adds less than a minute.

## Repository layout

| path | contents |
|---|---|
| `make.ml`, `check.ml` | load the development; load it and print the main results |
| `src/` | the development, 1,090 files and about 1.7 million lines; see `doc/LAYOUT.md` for the file families |
| `audit/` | the statement audit; see `audit/README.md` |
| `holtrace/` | scripts that re-check everything with HOLTrace; see `holtrace/README.md` |
| `doc/REPORT.md` | comparison of the sources, the Lean formalizations and this development: statements, architecture, results, checking |
| `doc/SOURCE_NOTES.md` | the errors, gaps, imprecisions and typos found in the sources, with how the formalization handles each |
| `doc/results.tsv` | one row per numbered result of Morgan-Tian and Moise that the development formalizes or replaces: source location, Lean declarations, HOL theorems and files, status |
| `doc/LAYOUT.md` | the file families of `src/` and the chain of the main intermediate theorems |
| `doc/timing.tsv` | load time of each file |

## Independent re-checking

HOL Light's core, Multivariate and the whole development were recorded as [HOLTrace](https://holtrace.cr.yp.to/)
proof traces, in 11 parts: 666,601,455 primitive inferences in 20.09 GB of traces (as written, not pruned), made
with the HOL Light commit given in `doc/REPORT.md`.

- HOLTrace's C checker, written independently of HOL Light, accepted every part.
- The parts were then replayed through HOL Light's kernel, all in one fresh session (checkpointed once with DMTCP
  and restored across a reboot) of a copy whose kernel files are unchanged, after the readable statement files had
  been loaded.
  - The kernel matched the traces' definitions of all the statement constants against those files.
  - Each axiom by which a part stands for a theorem of an earlier part was matched with that theorem, restored
    from the earlier part; no axiom was added.
  - It re-derived POINCARE_TOP, POINCARE_SMOOTH, POINCARE_EMBEDDED and MOI_SST_HEADLINE, each with no hypotheses
    and the required conclusion; the session's axioms were the three standard ones.

`holtrace/README.md` explains why the development was traced in parts, gives the details and a script that
reproduces the check.

## Provenance

- The formalization follows the proof architecture of Morgan-Tian for the smooth form (Ricci flow with surgery
  and finite extinction) and of Moise for the smoothing of topological 3-manifolds. It departs from their routes
  in places; `doc/REPORT.md` explains where.
- Further sources, cited in the files where used: Colding-Minicozzi on finite extinction, Kleiner-Lott's notes
  on Perelman's papers, and textbooks by Lee, Petersen, Chow-Lu-Ni, Ahlfors, Hatcher, Evans and Jost, and papers
  of Sacks-Uhlenbeck and Schoen-Uhlenbeck.
- The two Lean 4 formalizations of the conjecture, qinz1yang/differential-geometry and
  frenzymath/PoincareConjecture, served as references for statements and for the overall architecture; no code
  was taken from them.
- The smooth-calculus definitions (`continuously_differentiable`, `smooth_map_on`) and a few files of smooth
  calculus come from the Navier_Stokes development
  ([github.com/hol-light-family/Navier_Stokes](https://github.com/hol-light-family/Navier_Stokes)), where they
  originate in a HOL Light prototype by the project's initiator.
- A few general lemmas were adapted from earlier HOL Light work.
- The formalization was produced in November 2026 with Claude (Anthropic) through Claude Code, as a multi-agent
  project directed by its initiator.
