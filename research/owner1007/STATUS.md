# Structural Sokoban results

Research is paused at the owner's request. The results below were compiled
and independently replayed before publication. Preparing this update did
not rerun Lean, leanchecker, the source verifier, or diagnostic scripts.

## Current proved bounds

| Original map | Universal lower bound | Checked upper witness | Result |
| --- | ---: | --- | --- |
| soko1-1 | 328 | 342 pushes, 714 moves | 328 ≤ P ≤ 342; unresolved |
| soko1-2 | 231 | 235 pushes, 578 moves | 231 ≤ P ≤ 235; unresolved |
| soko3-2 | 141 | 141 pushes, 610 moves | Exact minimum P = 141 |

The original five exact results remain unchanged: soko2-1 = 109,
soko2-2 = 87, soko3-1 = 136, soko4-1 = 80, and soko4-2 = 85.

P counts initiated pushes from the canonical start of the complete original
map in the unchanged model. Boulder absorption, holes, and rolling traps are
preserved. Each lower bound quantifies over every completing legal Trace.
Upper bounds are explicit checked traces. Their movement counts are witness
lengths, not proved movement minima.

## Main proof entry points

- [soko1-1 interval](Owner1007/Interval11_328.lean),
  [universal lower328](Owner1007/Lower328.lean), and
  [342-push witness](Owner1007/Witness11_342.lean).
- [soko1-2 interval](Owner1007/Interval12_231.lean) and
  [universal lower231](Owner1007/Lower231.lean). Its235-push witness is the
  original unchanged `NetHack.Sokoban.Generated.Soko12Macro235M578Solution`.
- [soko3-2 exact minimum](Owner1007/Optimal32_141.lean),
  [universal lower141](Owner1007/Lower141.lean), and
  [141-push witness](Owner1007/Witness32_141.lean).

## Why the new bounds hold

For soko3-2, four local access phases force an additional owned cost. Parity
and the number of surviving boulders exclude140 pushes. A manually scheduled
141-push trace attains the resulting bound.

For soko1-1, any hypothetical completion with at most327 pushes forces an
actual190West189 event. Original186 is at184, original188 at186 or187, and
original212 at213 or214; gates137/139 are untouched. Six selected original
identities must all be consumed. Four manually prescribed walking components
classify their first push. Every head is impossible or reduces frame ranks
[1,0,2,1] through187West186 or214West213. The canonical activation and the
finite event-order induction prove that327 is impossible. No global
boulder-state search is used.

For soko1-2, both original first-push branches require231. The North proof
extracts a real S211 stage and a real first J event from every hypothetical
completion of at most230 pushes. Actual quietness preserves the required
boulder identity through the intervening prefix. Two J events exceed the
available owned budget; the critical264South290 alternative instead costs
at least232. Upper motion is allowed throughout this argument.

## Further proved restrictions

These are conditional results, not stronger universal bounds:

- An actual canonical North first265South branch costs at least232
  (`North265Price23212`). A local trade retains either Lower11 or Lower10
  with two survivors. The latter occupies both spare places and forces
  the entire Right group to be consumed.
- An actual North FirstJ packet with original S energy at least2 costs232
  (`NorthFirstJPrice23212`); a subsequent318West park costs233
  (`NorthFirstJPark23312`).
- For a hypothetical soko1-1 completion with at most328 pushes,
  `Budget32811.modes` retains exactly four Upper/Left/Rest alternatives:
  (6,4,3), (6,6,1), (8,4,1), or (9,4,0) with surviving Upper ownership.
  `UpperNineOnly14111` proves that Upper9 leaves only the untouched original141,
  with energy7; pair139/191 has energy2 and group137/188/193 has energy0.
- `Spare315Rest11` and `RightParkedRestInduction11` generalize the local
  spare-capacity and four-frame obstruction under Rest<2 without the old
  total327 threshold. They do not establish universal329.

## Evidence and trust scope

The toolchain remains Lean4.33.1, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. The axiom allowlist remains
`propext`, `Classical.choice`, and `Quot.sound`.

[VALIDATION.json](VALIDATION.json) summarizes pre-existing successful
compilations and independent replay records; [BUILD_RECORDS.json](BUILD_RECORDS.json)
retains their exact commands, source and output hashes, timings, and log hashes.
Compilation of dependencies is distinguished from separate module replay.
No generated but uncompiled Lean source is included in this update.

The original baseline `roots.json`, manifest, maps, semantics, five exact
results, and historical full-build receipts are unchanged. There is no new
all-eight-roots full-build PASS receipt. The detailed [invariant notebook](INVARIANTS.md)
retains rejected hypotheses and diagnostic counterexamples with their scope.

## Unresolved work

Two intervals remain open. A witness alone does not establish optimality;
conditional branch bounds do not replace a universal original-start theorem.
The three-map objective remains incomplete and paused. Unfinished coaccess
hypotheses and uncompiled scratch work are outside the proved results.
