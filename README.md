# NetHack Sokoban proofs

Lean 4 proofs of push-count bounds for all eight original NetHack Sokoban
maps, with exact minima for six maps, complete winning paths for every map,
and additional results about movement costs and reflections.

The project formalizes a restricted, deterministic puzzle profile of NetHack
5.0. Every bound refers to the full original map and its canonical starting
state within that profile. The repository contains the proof sources, pinned
map inputs, map generators, statement and axiom audits, a reproducible verifier,
and records of a completed verification build.

## Results

Let `P` be the minimum number of initiated boulder pushes needed to fill all
original pits and holes. The current proved results are:

| Map | Proven lower bound | Winning-path pushes | Moves in that path | Result for `P` |
| --- | ---: | ---: | ---: | --- |
| [soko1-1](research/owner1007/Owner1007/Interval11_328.lean) | 328 | 342 | 714 | `328 <= P <= 342` |
| [soko1-2](research/owner1007/Owner1007/Interval12_231.lean) | 231 | 235 | 578 | `231 <= P <= 235` |
| [soko2-1](lean/Audit/Soko21.lean) | 109 | 109 | 475 | **`P = 109`** |
| [soko2-2](lean/Audit/Soko22.lean) | 87 | 87 | 238 | **`P = 87`** |
| [soko3-1](lean/Audit/Soko31.lean) | 136 | 136 | 270 | **`P = 136`** |
| [soko3-2](research/owner1007/Owner1007/Optimal32_141.lean) | 141 | 141 | 610 | **`P = 141`** |
| [soko4-1](lean/Audit/Soko41.lean) | 80 | 80 | 299 | **`P = 80`** |
| [soko4-2](lean/Audit/Soko42.lean) | 85 | 85 | 332 | **`P = 85`** |

The lower bound applies to **every completing legal trace** in the model. The
upper bound comes from an explicit winning trace. Equality proves the exact
push minimum; only the intervals for `soko1-1` and `soko1-2` remain open.
[Research results](research/owner1007/RESULTS.json) index the new theorems.
[roots.json](roots.json) and the original `lean/Audit/` roots retain the
historical baseline bounds: 321–375, 220–235, and 140–147 for the three
updated maps. Their statements and certificates have not been replaced.

A **push** is the action that starts a boulder moving. A rolling-boulder trap
can carry it across several cells for that single push. A **move** is one
successful hero displacement, including a displacement that pushes a boulder.
These move counts do not represent full-game turns or prove minimum movement.

NetHack names the floors in reverse traversal order: `soko4-*` is the first
floor entered from the main dungeon; `soko1-*` is the upper, reward floor.

### Animated winning paths

![soko2-2 solution: 87 pushes and 238 moves](docs/animations/soko2-2.gif)

**soko2-2:** 87 pushes (proved minimum), 238 moves; about 35 seconds.
This is the shortest animation. All eight winning-path GIFs are in
[docs/animations](docs/animations).

Regenerate them with `python3 scripts/render_solutions.py` (Python standard
library only). Source paths and counts are recorded in the
[manifest](docs/animations/report/manifest.json). The animations replay the
published witnesses; no new Lean verification or solution search was run.

## Work completed

### Original maps and executable semantics

All eight complete Lua maps were extracted from upstream NetHack commit
[`b0c09c878e1f9f62bc7ab20e6edafd6108c325a0`](https://github.com/NetHack/NetHack/tree/b0c09c878e1f9f62bc7ab20e6edafd6108c325a0).
The extraction preserves map rows, coordinates, boulders, pits, holes,
rolling-boulder traps, doors, stairs, and entry metadata. The canonical start
is the branch entry on floor 4 and the downstairs entry on floors 1 through 3.
Each Lua input has a SHA-256 pin; [Maps.lean](lean/NetHack/Sokoban/Maps.lean)
is regenerated from those inputs.

[Model.lean](lean/NetHack/Sokoban/Model.lean) defines finite boards, states,
legal steps, execution, completion, and both costs. It includes:

- Eight walking directions, orthogonal pushing, explicit two-dimensional
  bounds, and the two-sided diagonal corner restriction.
- Consumption of one boulder when filling a pit or hole.
- Automatic rolling on the original rolling-boulder traps.
- An inductive `Trace` relation and a soundness theorem turning checked
  executions into traces.
- Structural step lemmas, exact move accounting, and composition of checked
  path chunks.

### Complete winning-path certificates

Every map has an explicit sequence of individual hero directions, a final
state, a trace theorem with both costs, and a theorem that the goal holds.
Long paths are split into smaller generated proof blocks and composed in Lean.
The table above records the current packaged witnesses, including later
improvements over the initial development paths.

External search was used to propose paths and certificate data. The proofs
check the resulting full paths; they do not assume that a searcher's first
solution is optimal or that its pruning and state compression are complete.

### Universal lower bounds

The lower-bound infrastructure proves local inequalities for every admitted
model step and combines them along arbitrary legal traces. For a typical
potential `V`, the key obligations are:

```text
V(before) <= step.pushCost + V(after)
Goal(final) implies V(final) <= 0
```

Telescoping these inequalities gives `V(initial) <= total pushes`.

The development extends basic potentials with pattern projections, hazard
phases, ghost-boulder abstractions, player-sensitive corrections, finite
residual tables, disjoint credits, decision DAGs, and compact encodings.
Soundness lemmas connect these certificates back to the original `Trace`
semantics. Generated finite checks are discharged inside Lean.

The current lower-bound entry points include:

| Map | Main lower-bound implementation |
| --- | --- |
| 1-1 | [Structural separator and event-order proof yielding 328](research/owner1007/Owner1007/Lower328.lean) |
| 1-2 | [Disjoint owned costs and first-event proof yielding 231](research/owner1007/Owner1007/Lower231.lean) |
| 2-1 | [Pattern certificate yielding 109](lean/NetHack/Sokoban21/Soko21Optimal.lean) |
| 2-2 | [Hazard/player correction yielding 87](lean/NetHack/Soko22Hazard87/LowerBound.lean) |
| 3-1 | [Guarded residual correction yielding 136](lean/NetHack/Soko31Optimal136/Verified.lean) |
| 3-2 | [Persistent token costs, parity and capacity yielding 141](research/owner1007/Owner1007/Lower141.lean) |
| 4-1 | [Pattern certificate yielding 80](lean/NetHack/Sokoban41/Soko41Optimal.lean) |
| 4-2 | [Pattern certificate yielding 85](lean/NetHack/Sokoban/Soko42Optimal.lean) |

[Reduction.lean](lean/NetHack/Sokoban/Reduction.lean) also proves exact trace
splitting and composition, transfer of lower bounds after a checked prefix,
and optimality of suffixes of an attained push-optimal solution.

### Structural improvements from the original canonical starts

The new proofs track original boulder identities, disjoint costs, player
components, irreversible hole filling, and the order of necessary exits.
Small corral lemmas describe fixed occupancy patterns and the walking
components they confine. They connect to arbitrary completing traces through
first-event arguments; they do not enumerate the full original state space.

For `soko3-2`, a four-phase access argument, parity, and the required number
of surviving stones strengthen the universal lower bound to 141. A manually
scheduled, explicitly checked 141-push trace attains it.

For `soko1-1`, any putative solution with at most 327 pushes forces a specific
190→189 push and one of four six-boulder frames. Each frame's first selected
push is impossible or strictly decreases a rank. This finite event-order
obstruction proves the universal lower bound 328. A separate 342-push trace
provides the upper bound.

For `soko1-2`, both possible original first-push branches require at least
231 pushes. The North branch uses actual boulder ownership and quiet-prefix
transport: two necessary J events exceed the available budget, while the
remaining critical 264→290 event has a disjoint cost of at least 232. The
235-push witness remains the upper bound. Stronger conditional branch bounds
are recorded separately; they do not establish a global bound above 231.

See the [English status](research/owner1007/STATUS.md),
[invariant notebook](research/owner1007/INVARIANTS.md), and
[recorded validation](research/owner1007/VALIDATION.json). Research is paused
at the owner's request. Two optimality intervals remain unresolved.

### Movement costs and distinct optimization objectives

For `soko4-2`, [Movement/Claims.lean](lean/NetHack/Sokoban/Movement/Claims.lean)
establishes three achievable `(pushes, moves)` pairs:

| Witness | Proven consequences |
| --- | --- |
| `(85, 332)` | Push-optimal; dominated by `(85, 322)` |
| `(85, 322)` | Push-optimal; improves the original witness by 10 moves |
| `(92, 319)` | Fewer moves than either 85-push witness; not push-optimal |

The last two costs are incomparable componentwise. Their existence does not
establish a complete Pareto frontier or an exact global movement minimum.
The proved global movement interval is `85 <= minimumMoves <= 319`.

There is also a genuine exact movement result from a particular reachable
late state: [Movement/Late.lean](lean/NetHack/Sokoban/Movement/Late.lean) proves
that its continuation needs exactly **8 moves** and **2 pushes**. This is a
result about that reached state, separate from the original-start minimum.

### Reflections and optimal continuations

The symmetry infrastructure proves that board and direction isomorphisms
preserve legal traces, completion, and both costs. Concrete horizontal,
vertical, and combined reflections are checked for `soko4-2`.

[Soko42AllOrientations.optimal](lean/NetHack/Sokoban/Symmetry/Soko42AllOrientations.lean)
transfers the 85-push lower bound and an 85-push/332-move witness to all four
creation orientations. It also proves push-optimality of every remaining
suffix of those paths. This concrete four-orientation result concerns `4-2`;
the other maps' result table uses their canonical orientations.

### Source validation during development

The development included independent checks against the pinned upstream
sources: literal extraction of all eight maps, 16 executions of the actual
Lua map files covering both reward-selection branches, and bounded C probes
of the original predicates. The reported C checks covered 4,990 `bad_rock`
fixtures, 1,659 rolling-trap generation positions, and 97 completion cases,
with address and undefined-behavior sanitizers.

Further checks compared the executable Lean model with an independent Python
implementation and audited the C branches exercised by concrete full paths.
These are finite development-stage checks. They do not establish a universal
C-to-Lean refinement theorem, and the historical path audits cover their
specific witnesses rather than automatically covering every later improvement.

This package includes the literal extractor and Lean map generator. The
development-only C/Lua probes, independent model runner, and search tools are
not included; the older executable-model
[notes](lean/validation/sokoban/model/README.md) describe that broader setup.
The verification commands below require only the files shipped here.

## Scope of the model

The completion condition is `Goal state := state.holes = []`: every original
pit and hole has been filled. Travel to stairs, opening reward doors, collecting
the reward, and winning the full game are separate objectives.

The admitted profile assumes an ordinary capable ground-based hero and
excludes monsters, interfering objects and statuses, tools, teleportation,
exotic movement, new boulders or traps, squeezing under or past boulders, door
opening or breaking, and voluntarily entering an unfilled pit or hole.

A roll stops at a wall or the first open pit/hole. A transition whose roll
would collide with another boulder or an intact door is excluded. Momentum
transfer, stacked boulders, and door breaking in the full game are outside
this model. The bounds quantify over all legal traces of this explicit
profile; they are not unrestricted full-game NetHack optimality results.

## Verification and trust

The package contains **17,853 Lean proof modules**, totaling about **930 MB**
of source, plus eight audit modules. Most of the volume is generated finite
certificate data. The import closure depends only on the pinned Lean core
library; there are no Mathlib or other Lake package dependencies.

[scripts/verify.py](scripts/verify.py) checks the toolchain pin, file manifest,
exact import closure, source restrictions, and byte-for-byte map regeneration.
Its build mode compiles every required module from source using one Lean
process at a time and an isolated `LEAN_PATH`. For each root it checks the
statement audits and `#print axioms` output, and runs supplementary kernel
replay with `leanchecker`.

The axiom allowlist is `propext`, `Classical.choice`, and `Quot.sound`.
The source gate rejects proof placeholders, `native_decide`, custom axioms,
unsafe declarations, and the other escape mechanisms listed in the verifier.
The trust boundary includes Lean's kernel and core library, the pinned
toolchain, the verification tooling, and the correctness of the stated model.
Search heuristics and generated certificate proposals supply no trusted
optimality premise.

### Recorded full build

A clean source build of commit
[`d93ec12331ef5fd9fb4f6288d9007c5ed97d89fe`](https://github.com/somethingnew179/nethack-sokoban-proofs/commit/d93ec12331ef5fd9fb4f6288d9007c5ed97d89fe)
started on **2026-11-06 at 17:37:01 UTC** and completed on **2026-11-11 at
22:52:12 UTC**, with one recorded resume. All **17,853 modules** compiled
successfully, all **eight root audits passed**, and the receipt reports no
failed compilation attempts or other problems.

The original evidence is preserved under
[receipts/baseline-d93ec123/](receipts/baseline-d93ec123):

- [Verification receipt](receipts/baseline-d93ec123/VERIFICATION_RECEIPT.json)
  with toolchain, environment, timings, hashes, and per-root results.
- [Original source manifest](receipts/baseline-d93ec123/MANIFEST.sha256).
- [Compressed per-module records](receipts/baseline-d93ec123/modules.jsonl.gz).
- [Statement and axiom audit outputs](receipts/baseline-d93ec123/axioms).

The records were cross-checked against the baseline tree when preparing this
README. The existing `lean/` proof sources and Lua inputs remain byte-identical to
that baseline; the new proofs are added under `research/owner1007/`. Removing the historical Russian-language reports and updating the
packaging script changed the current manifest, so the archived receipt stays
attached to its original commit and manifest. It is not a verification of
the new research roots. Those roots have separate recorded kernel compilations
and `leanchecker` replays. This results-publication update reuses that existing
evidence and does not rerun Lean or claim a new full-tree PASS receipt.

## Reproduce verification

Requirements: Git, Python **3.10 or later**, a Unix-like system with `os.wait4`,
and Lean **4.33.1** at commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. The Python tools use only the
standard library. With Elan installed, the pinned toolchain can be installed
as follows:

```sh
git clone https://github.com/somethingnew179/nethack-sokoban-proofs.git
cd nethack-sokoban-proofs
elan toolchain install leanprover/lean4:v4.33.1

# Check inputs, closure, source restrictions, and generated maps.
python3 scripts/verify.py check

# Compile and audit all eight roots from a clean checkout.
python3 scripts/verify.py build --build-dir ../nethack-sokoban-build

# Record the completed build, then cross-check its records.
python3 scripts/verify.py receipt --build-dir ../nethack-sokoban-build
python3 scripts/verify.py check-receipt
```

The build directory must initially be empty. An interrupted build can be
resumed by rerunning the same command with the same directory; retained
compiled files are rehashed on resume. Keep the source tree unchanged during
the build. The verifier requires a clean Git checkout for a passing receipt.

For a smaller first run, select a single root in a separate build directory:

```sh
python3 scripts/verify.py build --build-dir ../nethack-sokoban-build-42 --root 4-2
```

A single-root run does not establish an all-eight-roots PASS receipt.
`check` does not compile the proofs, and `check-receipt` only checks recorded
results. A fresh verification requires `build`.

The full build is substantial: the baseline accumulated about **78.5 hours**
of module-compilation wall time. Its largest recorded compiler RSS was about
**3.49 GiB**. Defaults are an **8,192 MiB** per-process Lean memory limit and
a **7,200-second** timeout per module. Keeping all compiled `.olean` files
would require about **6.64 GiB** for the baseline outputs; by default the
verifier deletes outputs no later root needs. Allow additional space for the
source tree and records. See `python3 scripts/verify.py build --help` for
resource controls.

The map inputs can also be checked separately from `lean/`:

```sh
cd lean
python3 validation/sokoban/source/extract.py --check
python3 validation/sokoban/source/generate_lean.py --check
```

## Repository layout

| Path | Contents |
| --- | --- |
| `dat/` | Eight unmodified upstream Lua maps and the upstream license |
| `lean/NetHack/Sokoban/` | Model, generated maps and paths, generic certificate machinery, interval roots, movement and symmetry results |
| Other `lean/NetHack/Soko*/` directories | Map-specific lower-bound certificates and witness proofs |
| `lean/Audit/` | Readable statements, source pins, witness checks, and axiom audits for all eight maps |
| `lean/validation/sokoban/source/` | Literal extraction, generated map data, and Lean map generation |
| `roots.json` | Historical baseline bounds, theorem names, source pins, build order, and allowed axioms |
| `MANIFEST.sha256` | Integrity manifest for the current packaged inputs and tools |
| `scripts/verify.py` | Source checks, isolated sequential build, audits, and receipt generation |
| `scripts/package_from_source.py` | Packaging recipe for the development source tree; unnecessary for verification |
| `receipts/baseline-d93ec123/` | Immutable records of the completed baseline verification |
| `research/owner1007/Owner1007/` | Previously compiled structural proofs and improved winning traces |
| `research/owner1007/RESULTS.json` | Current research bounds and theorem entry points |
| `research/owner1007/VALIDATION.json` and `BUILD_RECORDS.json` | Existing selective compilation and replay evidence, reused without rerunning Lean |

### Selective research builds

The commands above operate on the original baseline roots in `roots.json`.
To compile the current research entry points separately, use:

```sh
python3 research/owner1007/selective_check.py \
  Owner1007.Interval11_328 Owner1007.Interval12_231 \
  Owner1007.Optimal32_141 --cache /tmp/nethack-research-lean4331 \
  --memory-mb 8192
```

The helper resolves imports from the unchanged `lean/` tree and the added
research sources, checks cache identities against the source and toolchain,
compiles missing dependencies sequentially, and runs `leanchecker` on the
requested roots. The published [build records](research/owner1007/BUILD_RECORDS.json)
and [validation summary](research/owner1007/VALIDATION.json) describe the
checks already completed before publication. No check was rerun to prepare
this commit.

## Remaining work

The open push-count intervals are **`328 <= P <= 342`** for `soko1-1` and
**`231 <= P <= 235`** for `soko1-2`. `soko3-2` is closed at **141 pushes**.
The other five exact minima are unchanged. The research is paused; the
three-map objective is not marked complete.

- Close the intervals for `soko1-1` and `soko1-2`.
- Determine original-start movement minima and, where relevant, lexicographic
  optima and Pareto frontiers.
- Extend concrete reflection coverage beyond `soko4-2`.
- Extend the admitted physics and gameplay profile and establish a universal
  correspondence with the upstream C implementation.

## Attribution and licensing

NetHack map inputs are pinned copies from the upstream project.
[LICENSE](LICENSE) reproduces the NetHack General Public License.
[NOTICE.md](NOTICE.md) records upstream attribution, the provenance of the
Lean sources, and the licensing status of the remaining proof code.
