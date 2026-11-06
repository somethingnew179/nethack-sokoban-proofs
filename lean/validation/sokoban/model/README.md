# Executable Sokoban model

`NetHack/Sokoban/Model.lean` defines the pure puzzle profile used by the
certificates. It uses the complete extracted maps in `Maps.lean`, flattened
coordinates with explicit two-dimensional bounds, eight walking directions,
orthogonal pushing, the original two-sided corner restriction, and consuming
one boulder when filling a pit or hole.

The original 5.0 rolling-boulder traps are retained. A push onto one can roll
several cells automatically; that costs **one initiating push**, not one push
per traversed square. The admitted roll stops at the first open hazard or wall.
The current restricted profile rejects a roll that would meet another boulder
or an intact door. Real momentum transfer, stacked boulders, and door breaking
are consequently outside this profile. It also excludes monsters, tools,
teleports, new traps/boulders, squeezing under or bypassing a boulder (including
the ordinary light-inventory case that incurs a luck penalty), exotic movement, and voluntarily stepping into
an unfilled pit/hole. Execution ends when all original pits/holes are filled;
travel to stairs after the original Sokoban flag is cleared is separate.

`run_sound` turns a checked path into an inductive `Trace`. `roll_spec`,
`pushBoulder_spec`, and `step_cases_floor` prove the exact object changes and
that every actual landing is contained in the finite static relaxation used
by the lower-bound checker. The latter retains the required support floor
behind each boulder. `step_holes_length` proves a push fills at most one
hazard. `run_moves_eq_length` proves the declared move cost of a checked path.
`run_append_of` permits kernel checking and composing finite chunks.

The JSON-line executable accepts `info`, `step`, `run`, and `targets`
operations. For example:

```sh
cd lean
lake build sokoban_vectors
printf '%s\n' '{"map":"soko4-2","operation":"info"}' | .lake/build/bin/sokoban_vectors
python3 validation/sokoban/model/check.py --per-map 500
```

The independent test implements coordinates and occupancy sets in Python
rather than reusing the Lean implementation or the searcher's push graph.
It exercises all eight original maps, their initial states, deterministic
random well-formed fixtures, and explicit rolling-trap cases. Its report
records source and native hashes before/after comparison. This is finite
Python/Lean evidence. Actual C predicate probes and source extraction checks
live separately in `../source/`; neither these tests nor the executable-model
proofs constitute a universal C-to-Lean refinement theorem.

The external searcher's compression and heuristics are proposal machinery.
Solution certificates check the full sequence of individual moves in Lean,
and potential certificates prove a bound for every admitted model step.
Those arguments do not trust the searcher's compressed graph or an assertion
that its first returned path is optimal.
