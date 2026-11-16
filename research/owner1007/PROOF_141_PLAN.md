# Closed soko3-2: kernel-checked exact minimum141

Goal remains exact minima for ALL THREE maps. Soko3-2 is closed; soko1-1 and
soko1-2 remain active. Do not stop at this intermediate milestone or a report.
No global puzzle-state enumeration. Parent remains sole writer. All original
Lean sources and witness354 are preserved.

The entire141 chain below is now proved in `Owner1007.Lower141`, compiled
and independently replayed with leanchecker. The exact original Trace statement
and axioms were printed; only the existing three allowed axioms occur.
`Owner1007.Witness32_141.solution` now gives the matching141-push/610-move
trace. `Owner1007.Optimal32_141.minimum_push_count` proves the exact minimum,
with the full source pin and allowed-axiom audit. All passed compile/replay.
This closes3-2, but does not complete the three-map goal.

## Current kernel-checked foundation

The new modules are under `research/owner1007/Owner1007/`, compiled with
`selective_check.py` into `/private/tmp/nethack-owner1007-lean4331/oleans`.
Each successful target also has a `leanchecker` replay. Source/toolchain/hash
validation occurs before cache reuse. Do not run two cache-writing checkers
concurrently. An agent may run Lean `--stdin` without output-file options to
perform read-only experiments against immutable cached imports.

* `FrozenDebt32`: locked sets appearing in a trace contribute their debt above
  scalar134. Pairs160/161→141;158/159→137;241/267→153;289/290→149;288/289→147.
* `TokenAccounting`: every original Trace has a Logged list of exact Matches
  outcomes. Pure persistent `endGroup`, `ownSlack`, `ownPushes`, `ownCredits`.
  Exact ledger: initialDebt+ownPushes=ownSlack+finalDebt+absorptionCredit.
* `TokenPartitions`: energy=ownSlack+finalDebt; exact disjoint additivity;
  whole-map energy=pushes−134 atGoal. No double-counted push or survivor.
* `TokenPersistence`: empty groups remain empty, singleton survivor has no
  absorption credit, survivorEnergy=initialDebt+ownPushCount. Zero own pushes
  means unchanged group. Also group update/slack monotonicity.
* `LockedTokens`: locked cells persist INSIDE their tracked group, so debts
  can be added to a disjoint group's credit.
* `LeftPhases32`: four symbolic phases for A, verified for every floor hero,
  direction and13 hole phases. One combined decide exceeded kernel memory;
  splitting into FOUR phase lemmas passed (58s total), with allowed axioms.
* `EnergyFrame32`: exact G/A/B energy decomposition, and G-energy≥5 even
  though the legacy ticket may forget139. Ghost ticket stays inside G.
* `LeftEnergy32`: local phases lift to all original reached states; if A has
  zero ownSlack then A-energy≥3. Therefore every completing trace withP≤140
  must spend ownSlack(A)≥1. This is a conditional equality restriction,
  This was the first part of the now completed universal141 proof.
* `TokenBounds32`, `Heavy32`, `GroupParity32`, `GateTokens32`,
  `GateSurvival32`, `TokenCounting`, `Lower141`: all remaining equality,
  parity, tiny history invariants and survivor counting are kernel checked.

Partition of original16 tokens:

```
G = [139,215,239,244,267,270,289]
A = [80,132,134,158,161]
B = [86,113,188,211]
```

## Mathematical chain, now formalized

SupposeP≤140. Exact total energy≤6, G-energy≥5, A-ownSlack≥1,
and all owned slack/debts are nonnegative. Hence:

* G-energy=5;
* A-ownSlack=1, A-finalDebt=0;
* B-ownSlack=0, B-finalDebt=0.

Do NOT infer G-finalDebt=0: token139 may have debt.

Split G into139 plus six heavy singleton tokens with initialdebt≥7.
Each heavy token cannot survive withinG-budget5. It cannot visit a debt0
cell either: on a surviving prefix its own slack would be initialDebt plus
at least one push, ≥8. Thus all its moves between positive-debt cells have
EVEN slack, and its fill has zero slack. The existing147 static stay frames
prove this parity with one finite universal check. Consequently139-energy
is odd/nonzero, so139 must move.

Movement139 requires original113 to leave113. For B-energy0, a surviving
zero-debt token has zero own pushes and stays put. If86 never moves and113
has ownSlack0, token113 is confined to113 or112: first zero move is113W112;
the only zero next move112S138 needs the player at occupied86. Equivalently
[86,112] is physically locked and would contribute forbidden B-debt1.
Therefore both original113 and86 consume.

Any positive-initial-debt A token surviving with finalDebt0 has ownEnergy
initialDebt+ownPushes. Budget1 excludes134/161; for158(initialDebt1), budget1
forces0 pushes, so it stays158 with debt1, contradiction. Positive B tokens
188/211 cannot survive energy0 either. Only80,132,139 can survive: at most3,
contradicting actual conservation16−12=4. This proves141.

## Exact four-phase A geometry

Three fixed tokens80,134,161. Two mobile token positions:

```
S0:132,158   S1:133,158   S2:132,159   S3:133,159
R={133,159,160}; player initially outsideR.
```

Zero own-slack transitions either stay in this four-phase family, or create
locked158/159(debt3) or160/161(debt7). No shadow walk entersR. NoBad route
would leave all5 A tokens alive, impossible atGoal. In particular the tempting
zero activation158E159,132S158 DOES openR, but also freezes158/159; never
omit that terminal cost.

## Original formal proof checklist, completed through141

1. DONE: tight budget equalities.
2. DONE: splitting, singleton energy domination, identity count.
3. DONE with a better recursive inequality: cheap_token_even needs no list
   of visited states or explicit prefix splitting. Header slack below current
   debt implies positive landing debt and the recursive cheap hypothesis.
4. DONE:139/113 and86/113 history invariants, final count≤3contrad4.
5. DONE: final universal141 statement, axioms, leanchecker replay.
6. DONE: matching141-push/610-move witness and exact minimum theorem.
7. ACTIVE: exact1-1/1-2. Closing3-2 is NOT completion of the three-map goal.

## Archived142 hypothesis, refuted by the matching witness

The proposed strengthening below was not proved. It is false: the new
original-model141-push witness parks113 EAST at114, leaving the86/112 passage
usable. Its survivors are80@80,132@106,139@113,113@114, all at debt0.
Owned energy is G5+A1+B1=7, exactly141−134. The explicit trace, not a search
exhaustion, settles the upper bound. The following records the abandoned idea.

Assume excess≤7. The old four-phase analysis plus refined low-cost exits may
show A-energy≤2 forces both original80 and132 to survive. The cheap activation
132N106 creates physical lock80/106; if80first goesN54, both tokens become
zero-debt survivors after the second unit. Cost2exits134W133 or161W160 leave
unavoidable terminal debt or fail to release the group, and should require
A-energy≥3. These branches need new compact local phase proofs.

Then G's six heavy tokens still consume withinbudget≤6. Remaining B-energy≤1
may force86/113 to either both consume or form86/112; coupling this to139's
own post-discard cost is the next candidate obstruction. No142 theorem yet.
