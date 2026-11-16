# Structural research, owner1007

Current proved bounds: soko1-1 **328–342**, soko1-2 **231–235**, and
soko3-2 **exact141**. Research is paused. This notebook preserves the
chronological development; earlier numerical bounds are historical steps.
See [STATUS.md](STATUS.md) for the final proved/unresolved distinction.
No proof check was rerun for publication.

All coordinates are zero based, cell = x + 26*y. No global boulder-state search
is used here. Walking BFS holds all boulders and holes fixed and has at most
the board's floor cells as vertices. Replaying explicit plans proves no lower
bound; Lean checks are reported separately.

## 3-2: where 147 loses against the scalar 134

The known witness has total scalar slack 12 and final surviving debt 1:
147 = 134 + 12 + 1. Positive slack events are:

| Push | Original identity | Displacement | Slack |
| --- | --- | --- | --- |
| 5 | (2,5) | (2,5) → (2,4) | 1 |
| 15 | (5,9) | (5,11) → (5,10) | 2 |
| 16 | (3,11) | (3,11) → (2,11) | 2 |
| 17,18 | (7,10) | (7,11) → (6,11) → (6,10) | 2+2 |
| 19 | (10,9) | (10,9) → (9,9) | 2 |
| 20 | (9,5) | (9,5) → (9,4) | 1 |

All later pushes have zero scalar slack. The original (9,4) stone ends at
(8,4), debt 1. This points to initial access/parking, not a per-hole surcharge.
Baseline140 combines134 with group7 credit5 and disjoint complementary
credit 1; new charges cannot simply be added to those same pushes.

Concrete cut candidates: (7,8) pushed south to (7,9) locks vertically with a
stone at (7,10). The diagonal bypass is blocked by both a wall and that stone.
Parking (3,11) north at (5,10) after routing it also conflicts with (5,9).
One must prove a disjunction between paid clearance and expensive survivors,
including cardinality of the four surviving stones. These observations are
candidates, not universal numerical theorems.

The old 5531-row group7 table is truncated at credit5. Initial inspection of
listed links did not show a cost5 completion; this did NOT establish a strict
gap. A continuation at the boundary explicitly refutes credit6: follow27
listed actions to ghosts[265,289], hero291, cost5, then21 zero-cost actions
consume both. `ghost5_counterexample.py` reproduces all48 enabled pushes and
146 walking moves, ending with no ghosts. This is an abstract counterexample,
not an original legal completion. No new boulder states were searched.

The initial obstacle pair188=(6,7),211=(3,8) blocks the actual player's access
to213, support for the abstract plan's first239south. Clearing either feeds a
stone into214=(6,8), which the cheap ghost schedule assumes available. A new
joint throat-capacity invariant must restore this interaction; increasing the
isolated group7 credit is mathematically impossible.

### Kernel-checked lower141

A different compact interaction closes one point without enlarging group7.
Split initial identities into G=old seven, A={80,132,134,158,161},
B={86,113,188,211}. Energy of a group means OWNED scalar slack plus its own
terminal debt. A Logged bookkeeping theorem proves exact additivity and
totalEnergy=P−134 for every original completing Trace.

IfP≤140, totalEnergy≤6 and the old G-ticket reserves5. At zero A-slack the
left pocket has only four symbolic phases (two mobile stones132/158, three
fixed stones); an exit creates a frozen A-pair158/159(debt3) or160/161(debt7).
Otherwise all five A-stones survive, contradicting four total survivors.
Therefore A must spend1. The budget is now tight: G-energy5, A-slack1,
and zero B-slack and A/B terminal debt.

The six heavy G-tokens have initial debt≥7. They must consume, and every
cheap trajectory of each has even slack. This is a recursive arithmetic
invariant plus147 static push-frame checks, not enumeration of trajectories.
Thus G139 must move to account for the odd5. Its move requires113 to move.
Zero B-energy forces113 to consume; zero-slack113 then needs86 cleared,
so86 also consumes. All positive-debt A/B identities consume. Only80,132,139
can survive—at most3, while conservation requires4. Contradiction proves141.

Full universal theorem: `Owner1007.Lower141.pushes_lower_bound`.
The matching witness is `Owner1007.Witness32_141.solution`:141 pushes,
610 moves. Park original113 EAST at114 instead of WEST at112; this preserves
the upper86/112 passage. The remaining deliveries can be scheduled without
the old reversals. Final survivors are80@80,132@106,139@113,113@114, all at
debt0. The exact group energies are G5+A1+B1=7. Only fixed-position walking
BFS was used to connect a manually prescribed141-push macro plan.

`Owner1007.Optimal32_141.minimum_push_count` proves the universal lower bound
and its attainment. It and the witness passed kernel compilation, full source
pin, allowed-axiom audit and leanchecker replay. **The exact minimum is141.**

## 1-1: avoid double counting late component switches

The witness repeats three 18-push component switches near its end. Identical
boulder and hole positions do not make these removable loops: the hero ends
in a different walking component. Initial tempting hypothesis: these 54
pushes explain the 375−321 gap. **Rejected after evaluating the actual 321
potential**: the hero-sensitive scalar already pays all three switches.

The entire 54 slack of that potential occurs in nine phase-0 pushes:
move 14: +2; moves 17,18,19: +2 each; move 72: +20; move 85: +2;
moves 100,101: +2 each; move 126: +20. The two +20 events push original
stones 212 and 139 from cell291 south. A useful new correction must remember
these early support preparations, not charge the late cycles again.

### Kernel-checked upper354/718, then342/714

First change (375→357): original139 is parked at292 instead of being routed
deep into the bottom chamber. Original137 parks291 and is delivered first;
139 is then pulled out by legal pushes (west to291, then the normal route).
Only original212 retains the expensive deep excursion.

Second change (357→354): original293 moves east ONCE to294 instead of three
times to296. Original321, already an unused stone, moves east once to322.
This opens the hero's right pocket: the diagonal321→296 has one blocked
orthogonal side322 and one clear side295, so the model admits it. The later
retrieval of293 now needs three west pushes instead of five. Net saving4−1=3.
All721/718 individual hero directions are explicitly checked by Lean, including
the two-sided diagonal rule, rolling and consumption. `make_witness11.py`
reproduces both proposals; the generated files are actual kernel-checked proofs.

Third change (354→342): avoid the deep212 excursion altogether. Before the
upper deliveries, move268 east twice to270 and266 east once to267. Then park
212 at293,139 at292,137 at291. Once the row7 stones have consumed, deliver137
first. Retrieve266 west twice to265 and deliver it; now212 can move north
from293 to267, west twice to265, then north. This frees support293 to retrieve
139 west from292. The three shallow parking cells suffice because their exits
are used in this order. The remaining deliveries follow the existing plan.
`make_witness11_342.py` contains this one explicit schedule; the generated
`Owner1007.Witness11_342.solution` passed kernel compile and leanchecker replay.
No original upper stone crosses from row11 to row12, and no upper stone is
sacrificed. Survivors remain original315 and321@322.

The additional268 east push is essential to THIS schedule: with268 only at269,
the player cannot stand at268 while267,293,294 are occupied. Moving293 farther
east instead leaves the final270 walking support inaccessible behind the
295/322 or296/322 corner cut. These are explicit failed schedules, not universal
claims. A proposed two-slot schedule with212 parked west at210 also fails:
the186/184 and188/186 retreat leaves support185 for the first east
retrieval in a sealed component. No lower bound follows from these failures.

Rejected355 shortcut: back188 west only once instead of twice, then deliver
it with one fewer east push. This blocks support187 for139south from213.
Delivering188 early is itself blocked by upper137. No355 theorem is claimed.

An unqualified claim that some upper-origin stone MUST enter row12 is also
false as a research hypothesis: an explicit alternative358/723 plan sacrifices
original133/135 and delivers315/321 instead. It was diagnosed by full Python
replay (`no_deep_diagnostic11.py`; not emitted as a Lean theorem). Thus a lower proof must charge
the disjunction between temporary deep storage and abandoning useful upper
stones; neither exact291south nor unconditional deep entry is universal.
Even the sacrifice branch is NOT a standalone20 charge: the old321 potential
resets all weights to0 at phase16, and that358 path's explicit sacrifice charge
is15 (6+2+2 initially, plus5 on the last fill). Its full excess37 includes other
parking and lower-stone costs. A valid improved bound needs shared accounting
of those alternatives; a claimed universal341 from either oversimplification
would be unsupported.

### Kernel-checked component-sensitive corral

The family L_t={188,189,213,t}, t=214,215,216, with three corresponding
upper player components, is invariant under arbitrary legal continuations.
The only permitted tracked moves shift t west, reducing the small rank.
All four tracked stones remain, contradicting the final two-stone budget.
`Corral11.excluded` is kernel checked. This eliminates an actual cheap
25-push first-fill prefix, but does not yet give a universal numeric increase.

### Fresh compact321 and one-way upper history

`TightSplit11.pushes_lower_bound` reconstructs321 without the old321
table: total owned hero/phase energy=P−315, pair139/191 reserves2,
pair186/212 reserves4, complementary14 energy≥0. For the latter pair,
the first west move costs2 and enters one of just two post-cuts; escaping
again costs2, or both survive and their initial debt pays at least4.
All finite geometry facts, the original315 foundation and the new root
were freshly compiled and replayed. Tightness at321 fixes the disjoint
energies to2,4,0 exactly.

The upper137/139/191 pocket has19 manually specified word/cut phases.
This is a symbolic invariant allowing arbitrary moves of the other15
stones and all original hole phases. Three overlap phases were necessary:
138/164/191,138/190/191,164/190/191; omitting them was incomplete.
Every exit is one of eight actor pushes of price2. A generic Logged
first-event theorem preserves the actual Quiet prefix, all original
directions, outcomes and initiated push counts.

The useful historical invariant is geometric rather than a phase-rank
table: no unpaid selected landing can be137,139 or191. Therefore, if
such a cell remains in the tracked group at the first event, its ORIGINAL
stone has never been pushed. This restores identity information lost
by an occupancy-only potential.

With original139 fixed, an owned-energy<2 original141 can only be141
or140. Every other viable move costs≥2 in the full hero/phase scalar;
arbitrary environmental moves have nonnegative retained-token price.
A successful139E140 rules out141-at140 and creates locked pair140/141.
Original139 survives, so its energy≥9. Likewise first191E192 creates
192/193 and original191 energy≥25. `StationaryGuards11` and
`StationaryExit11` prove these assertions for actual original Logged
prefix/head/suffix, including arbitrary hole changes.

For a3-or-more selected-stone corral, `CutEnergy11.future_energy`
reserves another2 after an exit: cheaper continuations preserve the cut,
contradicting the TWO total terminal survivors. This is a universal
continuation lemma, not just a failed schedule.

Now kernel checked and replayed: reserve4 for U6={137,139,141,188,191,193},
separately from left pair186/212 reserve4, proving UNIVERSAL323. If one of137/141/188/193
already spends2, pair139/191's independent2 suffices. Otherwise their
cheap guarded trajectories constrain the first upper event. Do not
claim4 for U4={137,139,188,191}:141/193 could pay to remove blockers
outside that group, invalidating the right-exit argument. The six-word188 history and all eight first-event cases are now assembled
in `UpperReserve11.upper_four`; `Lower323.pushes_lower_bound` and the explicit
`Interval11_323.interval` passed kernel compilation and leanchecker.

Failed341 variant: omit321E, move293 west to292 instead of east294,
then try the same317 garage. `diagnose341_failed.py` retains one explicit
macro schedule; its walking-only replay exits1 at the FIRST317east,
player369, because support316 is outside the walking component. The
blocking footprint includes266,292,317. This refutes that proposed
schedule, not every341-push completion and not a universal Rest lower bound.

## 1-2: bottom exit and survivor choices

Building blocks of the checked universal224: `North265Bound12.first265_cases` and
`AfterJBound12.firstJ_cases` handle the ACTUAL first210S,238S,265S
event and another mandatory owned event afterwards. They prove lower
group energy≥6, or≥5 with318 surviving. Together with Upper2 and
Right4/5 this pays224. They are conditional branches. The complete `Lower224.pushes_lower_bound`
now combines them with the checked remaining ring case for ALL original traces.

`Token213Gate12.cheap_crossing` proves that original213 energy≤1
forces an actual212N186 push after213W212, with support238 and
destination186 free. `VerticalPair12` reserves2 from either vertical
pair186/212 or160/186 on ANY original suffix, without requiring Goal:
either an owned push pays, or terminal debt pays. These constraints
may connect the residual ring263W262 to the upper cage. Removing
original108 from the cage is an unsound abstraction for the intended
entry classification: it gives access to top support134 prematurely.
The earlier claim that159S185 retains the oldUpper bonus2 was directly
rejected by Lean numeric checking and is not used.

`CageFour12.energy_four` is now checked and replayed: each of ten explicit
post263W262 access cuts forces owned future energy≥4. The cases pay an
ordinary2 plus disjoint unchanged Upper2, an Upper187N2 plus vertical-pair2,
the existing Gate19, a frozen four-stone square, or a terminal locked pair
with debt15/17. `NorthPrepared12` and `RingPrepared12` now also prove the actual tagged
prehistory that activates these cuts in every remaining cheap original trace.

The prehistory uses ten North footprints (five free371 positions ×213/212)
and four Ring footprints (265/239 ×213/212). An initial two-phase Ring
proposal missed free265N239. Keeping318 fixed was also false: free318E319
is accessible from317. The corrected Ring12-token footprint omits318,
retains238, and tracks original265 as a tag. Additional zero238N212 or
239N213 creates the original four-stone square186/187/212/213; reverse
265S291 or239S265 is paid. All14 walking closures, paid guards and exact
nonpaid tag-update tables passed kernel checks and root replay. Walking
BFS visits only fixed-board cells for these supplied footprints.

Base212 → witness235 has slack23 and final debt0. Concentration: bottom
stone (7,14) contributes8; early right clearance contributes1+3+2;
four left reversals contribute8; late parking contributes1.

Rejected candidate: every escape from the bottom chamber costs8 slack.
Counterexample prefix: push (7,14) east once to (8,14), then walk through
(7,13),(7,12),(7,11) into the left chamber. First exit costs only2 slack.

Rejected refinement: delivered bottom stone necessarily pays8. After moving
the original (6,12) stone out, the bottom stone can return west to (7,14),
go north to (7,11), west to (5,11), then north. That route can pay only2.
Thus neither a proposed225 nor222 bound follows from that argument.

Useful consequence: the known witness's early right delivery of the bottom
stone may be avoidable by delivering left stones first and retrieving this
stone through the left exit. An explicit reordered upper plan is being tested.

Those concrete attempts did not improve the witness. Parking the bottom stone
at292 or291 blocks the support291 required by old push45. Parking at290 permits
more of the path but blocks old push82; trying to retrieve it first requires
unreachable289. Omitting old pushes18/82 also fails at old push32, whose
support239 is inaccessible. These are precise failures of proposed schedules,
not universal impossibility arguments.

The six singleton frozen corners135,317,320,370,294,288 are now kernel checked.
`dead12_budget` proves that any distinct selected stones occupying those
corners in a reached, completable state have cardinality at most2. The shared
survivor budget prevents double counting separate corner penalties.

### Kernel-checked factorization and macro costs

The existing217 bonus factors for every hero and every Boolean pattern into
independent left/right functions. Eighteen circuit identities were proved by
512 cases of the nine LEFT Boolean inputs, leaving all right inputs symbolic;
no puzzle states or new search table are involved. The ordinary right term is
exactly2·[192 and193 occupied]+1·[141,168,271 all occupied].

Two local macros now have certified extra slack2 after paying the old bonus:
186N,N,W→133 (with160,134,133 initially empty), and187N→161 then186W→185.
Files CostPartition12Factor/CostPartition12Split passed kernel and replay.
The missing universal step is a complete event/cut classification that forces
enough such costs in every completing trace. Those macro lemmas alone did not
prove221; the later owned first-event proof below now proves222.

### Kernel-checked priced trap11, conditional lower223

Let E={105,106,131,132,157}. If the player is outside E and stones occupy
133,158,184, the cut admits three phases: [133,158,184], [132,158,184], and
discharged. Credits are11,11,0. The internal move133W132 costs2 but retains
the credit. The only exits are158W157 (base slack11) and132W131 (slack12).
Additional stones may restrict these moves; they cannot provide a cheaper exit.
The generic `PricedCorral.trace_price` lifts the finite local geometry to
arbitrary legal traces, including moves of unrelated stones. A completed board
has two survivors, so it cannot retain either three-stone phase. Hence every
completing suffix from this cut has scalar slack≥11, and the whole original
path has at least212+11=223 pushes.

`PriceTrap12.original_conditional_223` and the generic theorem both passed
kernel compile and leanchecker replay. The geometry check quantifies only
three symbolic phases, floor positions and directions. The physical regions
exclude the tracked boulder cells: allowing the player to stand on a tracked
stone would introduce impossible checker cases. At-M2048 the corrected finite
check exhausted memory; at-M8192 it passed in14.6s. This is a resource change
only; the checked theorem uses the original Model and existing axiom allowlist.
Activation of this cut is not universal. The separate proof below raises the
global interval to222..235. A plan may attempt upper access through a different
left macro or the east entrance. Those alternatives require a complete
first-entry classification before their prices can be combined.

### East-first branch225 and cheap-budget reduction

`FirstSplit12.original_first_push_split` proves that arbitrary initial walking
leads to exactly one of two first pushes,371N345 or371E372. In the east branch,
the token at372 progresses through373,374,348,322,296 to270. The cut also
retains192,193,218 and the player's outside component. Six positive phases
and a discharged phase carry credits6..0 after the first push. A completion
cannot retain four cut stones, so all six remaining corridor pushes occur.
`EastPrice225.correction_flat` verifies that these pushes do not change the
old217 correction: their sources and landings avoid its14-cell support, and
both player positions have the same bonus expression. Thus the credits add
to217 without charging the same bonus twice. The exact afterE potential is218;
the suffix needs224 pushes, giving225 including the first push. Kernel and
leanchecker both passed. This is a universal bound for the ENTIRE east branch,
not just for the packaged witness. `CheapNorth12` reduces anyP≤224 completion
to the exact north-first state.

For all original completions, `RightEnergy12.right_energy_three` reserves3
owned energy for seven original right identities. It transports the old
correction on only that group, with a new direct proof that rolling and
ordinary nonconsuming pushes preserve boulder/hole disjointness. It does not
rebuild or extend the old220 state DAG. Exact energy additivity then gives
leftEnergy≤5 wheneverP≤220. Each of the eleven ordinary left tokens has
initial debt≥7, so none can survive within that group budget: all must consume.
`LowBudget12.ordinary_consumed` checks this deduction in Lean. The remaining
task at that stage was to force enough left energy from consumption and access
order; the tight budget and conditional trap alone did not prove221.

### Universal lower222, kernel checked and replayed

Partition original identities into
U=[108,158,159,186,187], G=[210,237,238,263,265,318,371],
S=[213], R=[141,168,192,193,218,246,271]. Exact owned energy sums toP−212.
The old correction transported onto U reserves2. A seven-phase cut on
Q=[141,168,246,271] reserves2, and the disjoint old right pair/triple group
[192,193,218] reserves2, soR≥4. If original318 survives, R has at most one
survivor; three independent tiny cuts prove consumed246 costs3, consumed
141/168 together cost2, consumed271 costs1. ThusR≥5 in that case.

The ten explicitly listed Bottom=[318,371] phases reserve2 owned energy even
for an original PREFIX. Zero-price moves are the north/west word of371 or a
single east shift of318. The critical endpoint[318,291] seals player support317;
the alternatives[319,345] and[319,293] also seal the needed support. One final
zero branch creates the frozen horizontal pair[292,293]. Every other exit
costs≥2. In every retained phase the pair's terminal debt is≥2. This is a
component/debt invariant on ten hand-selected two-token patterns, not a BFS
over board states. The fixed-pattern walking components were proposed by BFS
over floor cells only, ignoring holes conservatively; Lean checks the whole
closure/price claim independently.

For the north-first branch, five cuts retain the seven G-stones while371
moves345→319→293→292→291. Every completion must contain one of five paid
exits. An original J=[210,237,238,263,265] exit costs2; J does not move before
this first event, so its price can be added to the independent Bottom2.
The exit371:291W290 costs2 and activates Ring=[210,237,263,290]. Four retained
stones cannot all survive; the ring forces a later ownedG price2. The formal
prefix/event/suffix decomposition proves the two prices are on separate
events. The remaining exit318W317 costs3 and leaves original318 locked;
R≥5 then supplies the missing point. Consequently G≥4, or G≥3 withR≥5.

Adding disjoint terms gives212+U2+G4+R4=222, or212+U2+G3+R5=222;
S-energy is nonnegative. The exact canonical north prefix is a legal two-move,
one-push original trace. It transfers this argument back to the initial state
without changing the push count. The checked first-push split and east225
bound cover EVERY original completion, including arbitrary initial walking.
`Lower222.pushes_lower_bound` and `Interval12_222.interval` passed kernel
compile and leanchecker replay, with only the existing axiom allowlist.
The current original-map interval is **222..235**; optimality is unresolved.

Useful failed strengthening: isolated Q-energy≥3 is false. A manually prescribed
ghost path spends only141E142 and271N245 and leaves two zero-debt survivors.
An isolated R-path similarly spends4 and leaves142/246. These paths process
only the selected group, not all18 original holes; they are not original
completions. A further increase must restore coupling to the remaining left
stones or use the shared survivor budget, rather than increase the same
isolated group ticket.

## Local path checks

`diagnose.py` implements the full executable rules, including pits/holes,
boulder consumption, rolling traps, eight walking directions, and the
two-sided diagonal corner restriction. It replays the three packaged paths
with the stated costs and final survivor identities. It then tries only the
same push-command list with one or two adjacent commands deleted, recomputing
walking routes. All1511 attempts fail to yield a completing trace. This is a
bounded local diagnostic, with zero enumeration of alternative boulder states.
Nineteen additional nonadjacent inverse pairs from the same identities were
also tested without success. These failures give no optimality certificate.

### Universal224 assembly completed

`NorthForcedRing12` shows that any hypothetical original completion withP≤223
must first pay371:291W290. The North prehistory preserves Upper5, fixedJ6,
and exact original213/371 tags. `RingPrepared12.ring_energy_six` is a universal
original-model continuation lemma from every one of the four corrected Ring
footprints, for any owned group containing it. Under energy≤5, Upper reserve2
and Ring reserve2 leave only1 for the S-token; the tagged first event must
therefore be263W262. Its2 and `CageFour12.energy_four`'s future4 contradict5.
Other possible first events pay2 plus an independent Ring2/Upper2 or create
a frozen four-stone square. No hypothesis about a chosen route remains.

The first371 event pays2, its left continuation pays6, and the disjoint
right group pays4: scalar212+2+6+4=224. East-first completions already require225.
`Lower224.pushes_lower_bound` and `Interval12_224.interval` both passed fresh
kernel compilation and leanchecker replay. The interval is224..235; equality
with an explicit winning trace has not yet been obtained.

### Stronger229 in the first318 branch

`SurvivorPrefix12` proves a compact monotonicity fact: for a token that
survives to the end, its energy cannot be smaller than its energy at an
earlier prefix, because initiated owned pushes cannot decrease and it
receives no hole-absorption credits. The real318W support forces original
371 already into a prefix position with debt≥4. Thus its whole energy≥4,
alongside parked318's3: the disjoint lower group reserves7, not merely5.

Both original bottom tokens survive, occupying BOTH terminal survivor
slots. Every right token must therefore consume. `RightConsumedEight12`
reserves independent costs2 for192/193/218,2 for141/168,3 for246 and1
for271, totaling Right8. Together with Upper2 and scalar212, the checked
first318 branch costs212+7+8+2=229. This strengthens one branch;
the universal minimum interval remains224..235.


### Retaining side stones instead of inventing independent tickets

The proposed isolated pair237/263 ticket2 is false as a relaxation:237E238
and263E264 each have zero scalar slack. `Pair23726312.matrix_rejected`
and `east_free` are kernel-checked negative diagnostics. They are not used
as a lower bound. Retaining264 instead yields `Sidecar26412.energy_four`:
the five-token cut210/237/263/264/290 must pay4. Its actual-model lifting
allows every other stone and any original reached hole phase.

A separate explicit six-token relaxation consumes the upper six stones
in47 initiated pushes/114 moves with owned energy2. It starts with player187
and stones108/158/159/161/186/212, leaves12 holes and is NOT a canonical
completion. `GhostUpperCounterexample12` certifies this diagnostic in the
original transition function. It rules out an unconditional isolated-upper4
claim; the actual210 and other retained side stones matter.

### Stronger leaves, with their missing universal links kept explicit

`StationaryGuardsSix11` extends the actual-history guards to energy<6:
while139 is stationary, original141 remains141/140; while191 is stationary,
original193 remains193/192. Therefore the first139E/191E leaves freeze a
selected survivor, whose debt alone contradicts totalUpper6<6.
`UpperEastSix11` checks these two leaves. On first216E217, original191
is still stationary and193 still blocks its easy escape. `RightFour11`
then reserves future4 for191/217; adding the head2 gives the third checked
leaf `Upper216Six11.reserve_six`. Other firstUpper leaves are unresolved;
these facts do NOT yet give a universal325 bound.

For1-2, retaining239 strengthens each of the ten old post263 cage cuts
from4 to6 (`Cage239Six12`). If187N occurs, the retained stone moves the
proof into a ten-cut post187 family;186W freezes a high-debt pair,212W
activates a four-stone trap, and the ordinary exits retain a separate
vertical pair. Actual263W support forces the moving ring token already
at239. Its head2 plus the stronger cage6 gives
`RingCageEight12.energy_eight`. This is only the critical263 branch;
other firstRing branches still prevent a universalRing7/8 conclusion.
`Quad28912` has eight hand-chosen cuts and a checked owned reserve5,
which may strengthen those branches. None of these are boulder-state BFS.


### Counting the next ordinary payment in the North leaves

`AfterJRecursive12` retains the first lower displacement instead of dropping
it when the next ordinary stone moves. After210S236,236S262 preserves a
seven-stone cut with the same five original371 phases. After either ordering
of210S236/238S264, another five-phase cut remains. Their next ordinary paid
head gives another2; if371 pays291W first, the retained cuts reserve4 or5;
if318 parks317, the original corridor traps a selected stone of debt≥4.
No initial lower payment is counted twice.

`AfterJDeep12.cash_cases_deep` therefore reserves ordinary4 or group5 from
the whole post210/post238 continuation. Lifting the actual first head gives
G≥7, hence `NorthJSeven12.firstJ_lower225`. The265 pipe uses fifteen manual
footprints: after291E292, freeing either plug costs4; a317 parking confines
a corridor token. `North265Eight12.first265_eight` gives G≥8 and the checked
`North265Count12.first265_lower226` gives226 canonical initiated pushes.
These are complete event branches, not the global225/226 lower bound.

The remaining global issue is activation: at hypothetical P≤224 the old
budget yields UP≤4,S≤2, whereas the old NorthPrepared theorem requires
UP≤3,S≤1. Improving a Ring continuation by itself does not justify using
that theorem with stronger budgets. Upper and S-token events before291W
must be handled jointly with the retained lower barrier.

### A successful cheap G-only relaxation diagnoses that activation gap

A prescribed custom afterN G-only start on the original board consumes all
seven marked G stones in87 pushes/246 moves with owned energy4 and11 holes
remaining. The sequence delivers238 before265 and318 before retrieving371.
This is a Python original-rule diagnostic, not a canonical winning witness
or a kernel theorem. It refutes a proposed independent G≥5 ticket and a
G4⇒318-survives claim for that relaxation. Upper/S access constraints are
essential; they must remain in the next universal statement.


### A false three-cell simplification on1-1

Dropping the neighbouring Pair would make a proposed original137 south-column
trap invalid. `Column137Probe11.prices_false` and `north_free` are checked
negative diagnostics:164N138,190N164 and216W215 all have zero actor price in
all sixteen active phases. The real obstruction is player access to their
supports, retained by the Pair and the marker. A fifteen-cut ranked proof
is being built with those components kept explicit; it is not yet a
universal325 lower bound.

`UpperResetBudget11.pair_four` is already checked: a first138E139/190E191
reset paysPair2 and restores a literal139/191 pair with futurePair2. Thus
Pair total≥4. Under hypothetical Upper6<6 this forces each remaining C-token
below2. `UpperResetHistory11` proves exact one-move barrier history using a
nine-node directed acyclic zero-word rank, rather than assuming a return
was the first move. `OneMoveGuards11` then applies to the moving barriers.


### Universal226 completed on the unchanged canonical1-2 map

The activation budget gap described above is now closed.
`NorthPrepared22612.prepared` starts from an arbitrary original afterN
completing Logged and hypothetical P≤225, with no assumed cheap-UP/S bound.
A real S212W211 prefix is preserved by five North211 cuts through arbitrary
other-token actions. The original S payment2 plus a G-event or Quad290
reserve contradicts the available joint budget. An early187N161 prefix
enters five North187 cuts;186W creates Gate19,161N pays8,212W feeds the
North211 theorem, and291W creates the checked RingUpper6 tail. The current
prefix cost2+head2+future6 totalsLeft10, exceeding theP≤225 Left budget9.
Every branch is an actual original-step split with tracked original tags.

With those exceptional prefix events excluded, only265S,318W,291W remain:
prepared210S/238S are blocked. The265 branch costs226,318 costs229, and
291W2 plus the unconditional localRing8 costsLeft10. The disjoint Right4
above scalar212 yields226. `North22612.canonical_bound` has no residual
route, budget, matrix or preparation premise.

The East branch needs independent ownership rather than adding an old
whole-corral ticket to an overlapping Right ticket. `East22612` checks
that192/193/218 are strictly blocked, have unchanged tags and ZERO owned
slack before the296N exit. The raw seven-phase certificate therefore gives
372's own prefix slack≥5;296N270 adds1. The original371East head already
paid2, so original371 owns≥8. Independent Upper2 and Right4 give226. No
Right push is charged to371.

`Lower226.pushes_lower_bound` combines BOTH actual first-push branches,
including arbitrary initial walks. `Interval12_226.interval` combines this
universal bound with the original235/578 winningtrace. Both roots passed
fresh pinned-kernel compilation and leanchecker replay. The current full
original minimum interval is226..235, not an optimality claim.


## Fresh milestone: seventh Upper6 case and stronger map12 gates

`Upper190EastSix11.upper_six` now handles the full actual first190E branch,
with no cheap-prefix or route premises in its statement. Under Upper6<6,
the head pays2 and resets the original3-token barrier. A second actual
first useful event is unavoidable. Resets retain a two-unit consumption
cut;190W enters Parked4;216E enters the two-token post cut. Generic
`UpperConsumedFuture11` uses actual consumption, not a guessed terminal
scalar debt. Stationary141/193 guards exclude the outward frozen-pair
exits. Kernel compile3.666s and independent replay passed. Seven of eight
first Upper events now reserve6; no universal325 is claimed until190W.

The remaining190W part has checked components: an eight-position188 word,
a bounded prefix-energy ledger, and `ParkedFourSix11.absurd`. The latter
makes the first useful Parked4 event explicit:137W pays the original137;
139E freezes a guarded pair;189W/190E/190W pays2 and enters a36-cut cover
with another2 inevitable if the tracked group consumes. This is a finite
symbolic corral statement for arbitrary untracked stones and all original
phases, not a certificate enumerating full game configurations.

For map12, `East22712.east_branch_227` is an actual original-afterEast
branch theorem. The marked original371 route pays8, Upper pays2, and
`RightEntryBound12` gives Right5 while the exact371 marker remains in270
or244. Retaining this marker matters: erasing the left environment permits
additional cheap right exits, so Right5 is NOT asserted unconditionally.

`FirstFill10812` has four chronological marker cuts108/82/56/30. Its fill
classification checks *all* foreign hole-target pushes. Every canonical
completing trace therefore first fills32 by original108 at30 pushing East;
all18holes/20stones are still present immediately before it. A direct
`Trace` decomposition also records exact before/head/after counts.

`Post187Seven12.energy_seven` reserves7 for
[158,159,186,161,212,210,237,262] and three short queue words. Eleven hand
cuts include frozen pairs and a free credit endpoint. It ignores108,238,
T and371 and does not need Goal. `Cage212Nine12.energy_nine` retains108
and replaces161 with187, obtaining9:187N costs2 then invokes Seven7;
212W invokes Quad15,237W/211N a frozen/Gate case, and262S costs7 while
the disjoint Upper5 retains2. Both are fresh kernel/replay checked. These
are local reservations only; North265 and cheap early activation still
limit the universal bound to226 until their actual cases are strengthened.

Additional bounded planning diagnostics: removing one or two adjacent
commands from the fixed342-push word tested683 variants and found no
legal completion. A single attempted340 schedule postponed original264
and tried to deliver it before137; its264E failed because support263 was
unreachable after lower parking. Neither failure proves a lower bound.
A zero-energy four-token central relaxation erased the other14 stones
and was stopped at a40-state cap (a24-state prefix was inspected). It
supplies no theorem or exhaustive certificate; it showed why a bare
independent central reserve loses the186/188 access coupling. Future
work should retain those barriers or explicitly couple their charges.


## Universal325 for the original soko1-1

All eight actual first useful Upper events are now covered.
`Upper190WordAfter11` classifies all eight cheap188 words; its187 case
already paid2 before the first190W head pays2 and Cover36 adds2.
The other possible words give a permanent survivor or Parked4, excluded
by `ParkedFourSix11`. `Upper190WestSix11.upper_six` therefore has only
originalLogged, Goal and the actual first190W event as premises.
`UpperUniversalSix11.upper_six` joins the eight exhaustive event cases.
`Lower325.pushes_lower_bound` applies it to every original canonical Trace;
315+Upper6+disjointLeft4+Rest≥0 gives325. `Interval11_325.interval`
retains the original full canonical342/714 winning trace. All five new
roots compiled and independently replayed with only the old axiomallowlist.
The remaining1-1 gap is17; the proof does NOT assert342 optimal.


## Post187 price8 and a corrected stationary-token hypothesis

`RingUpperReserveEight12.energy_eight` strengthens all three post187 frames
from6 to8. Its finite classifier includes *extra owned tokens*, especially
213South239, not just the literal12 lock positions. That extra head resets
the old T239 frame and costs2+old6. Omitting it made the first classifier
false; the corrected nine-head classifier and actual theorem passed the
kernel and leanchecker. The other delicate cases are265South followed by
one-phase `PostUpper29112.energy_six`,290West followed by`FarUpper12.energy_six`,
and213North creating globally locked161/187 of debt15. New stronger bounds
call OLD6/8 reset theorems; there is no cyclic use of the claimed improvement.
`T291Eight12` and `T239Ten12` also give actual originalRing265/239 South
branches cost10. Remaining S213263 branches still need a stronger charge
or an explicit survivor/capacity alternative before global227 is asserted.

The candidate implication Rest0⇒stationary321 was rejected promptly:
from the ORIGINAL canonical map, nineteen prescribed moves with a single
321West320 push have full18-token Hero315 energy0 and therefore Rest energy0.
315East/West and321East cost1;321West does not. The global326 work now tracks
the zero westward321 word instead of freezing it. This is a partial prefix,
not a completion and not evidence that a zero-Rest completion exists.


## A price-or-survivor invariant closes the actual first265 branch at227

`After265EastFive12` is a16-cut lower-pipe certificate, not a full-state
search. Its credit5 initially follows the three lower original identities
through their only support components. A stone entering corner320 has
zero scalar debt, so the old attempt to preserve credit5 by terminal debt
was false. The corrected local theorem returns either energy≥5, or
energy≥4 with a marked survivor. `After265Seven12` adds the actual head
and preserves that alternative; `North265Nine12` obtains G≥9, or G≥8
with an original G survivor. In the second case only one of the two final
survivor slots is available to the seven Right identities, forcing Right5.
Thus both alternatives give212+Upper2+G9+Right4=227, or
212+Upper2+G8+Right5=227. No event is charged twice. All continuation,
capacity and original-canonical first-event wrappers passed kernel/replay.
The16-cut module compiled290.583s in the root check; this was a bounded
local certificate check, not the old771288-node global DAG.

`North187Strong22612` and `NorthPrepared22712` now exclude early Upper/S
activation underP≤226, using the new first265227 and post187 reserve8.
The161North head alone costs8 for U while disjoint G always costs≥3,
so Left≥11 excludes the tight10 budget. `NorthLeftSurvival12` records a
useful global capacity rule: atP≤226, Left≥10 implies all13 original Left
identities consume; any Left survivor would instead force Right5.
These helpers are checked; the universal numerical lower remains226
until every original Ring event has reserve9 (or its survivor alternative).


## Universal227 and the stronger original Ring10 continuation

The S213 bottleneck closes by retaining the actual T-marker. With239
occupied,238East cannot open the support chamber. The first zero213West
activates the checked S212Nine cut; the expensive262South costs7 and
preserves disjoint Upper2. With T265,238East instead makes the globally
locked239/265 pair (debt15), while265North enters the retained239 cut.
`Cage239RetainedNine12` and `Cage265Nine12` both passed root kernel/replay.
This avoids assuming an unproved generic S213 price5 or a first-fill cost.

`After290Eight12` combines those cuts with the disjoint Upper2+Quad2895
on212West. The actual first290West therefore pays2+8=10.
`RingTen12.ring_energy_ten` covers EVERY first Ring event:263West≥11,
290West≥10,187North≥10,265South≥10,239South≥10,212West≥11,
and frozen-square branches have debt≥10. For212West, Upper2 and Quad2907
are disjoint tracked lists, proved additive before applying the head price2.
All assertions use arbitrary originalReached traces and actual owned outcomes.

`North22712.canonical_bound` uses actual P≤226 preparation. First265South
already gives227 by the price-or-survivor alternative;318West gives229;
210/238South are blocked. Remaining291West pays2 then Ring10, exceeding
the Left≤10 budget. `Lower227.pushes_lower_bound` joins this with the
actual East227 branch from the exact original first-push split.
`Interval12_227` retains the original235-push/578-move full-map witness.
These roots are freshly kernel checked and independently replayed. The
minimum remains unresolved in227..235; this is not an optimality claim.


## Universal228: preserve the early-S survivor instead of weakening it

`AfterJSurvivalRecursive12`/`Late12`/`Deep12` preserve the ordinary4,
group6, or group5-with-survivor alternatives already present in the old
local lemmas. No new geometry table was needed. `NorthJSurvival12` gives
G≥8 or G≥7 with a G survivor. With the actual paid S-prefix2 this gives
228 in both cases, because the survivor removes a Right slot.
`North211Priced22712` therefore excludes ALL actual earlyS211 events atP≤227.
Early187 events use their own price2 plus UpperAfter187 future2 (Upper4),
and `North187Strong22712` handles the remaining events with exact capacity.

`North265Joint22912` additionally retains Upper/S/238 from the actual
prepared prefix. The originalLower3 has9, or8 plus a survivor. The disjoint
Joint group costs4: cached Upper2 and a two-state vertical212/238 ticket2.
This gives229 for that actual first265 branch, with no hidden ticket premises.
`North22812` and `Lower228` combine those facts with the original first-push
split and Ring10. `Interval12_228` preserves235/578 as an upper witness.
All new universal roots passed pinned kernel and independent leanchecker.
Current original minima intervals (updated afterCycle32511):326..342,228..235,exact141; goal ACTIVE.


## Three disjoint future tickets and Ring11 (fresh root checks)

`FarUpperEight12` and `FarT291Eight12` retain three disjoint token lists:
UpperAfter187 (or original Upper), vertical212/238, and the far Ring.
Each has an unavoidable future price2 in the indicated player component.
A foreign paid move preserves all three, so its price2 adds to6 without
counting a token twice. The exceptional289West costs exactly5, rather than
the old weakened4. These certificates use the same small corral frames.

`PostUpper291Eight12` resets a zero291North exit into the OLD UpperRing8;
291South has its own price7 plus the preserved UpperAfter1872. The new
`RingUpperNine12` adds the Ring2 ticket even after the expensive161North8.
`T291Nine12` resets into the OLD Ring10, keeping the proof acyclic.
`After290Nine12` then yields9, and `RingEleven12.ring_energy_eleven`
yields11 for every actual first Ring event. Every new root passed pinned
Lean kernel and independent leanchecker. These are local arbitrary-reached
state lemmas; universal229 still needs the earlyS211 branch.

For1-1, `CoreStart11` links the canonical central first event to the
three-token LowerElevator frame while preserving the Rest zero budget and
the original317 identity. `Deep29133511.pushes_lower` proves that any actual
291South317 event in an original completing trace costs at least335 pushes.
`First137RestAnywhere11.rest_two` gives Rest≥2 for an actual first137West136
event, even when it is not the first Upper event. All these roots passed
kernel/replay. They do not yet establish universal326.


## P228 now forces earlyS211 and exactly Upper2

`NorthMain22912.event_lower229` proves229 for all actual first tagged
main events, with the fixed Upper/Core identities furnished by the real
North prefix. First291West now costs2+Ring11; Right4 supplies the last4.
`North187Strong22812` excludes early187North atP≤228. Its expensive161North
branch retains BOTH the original187North price2 and the later price8,
yielding Upper10; this repairs the older weakening to Upper8.

`NorthSNecessary22812.necessary_first_s` therefore proves that an original
afterN completing trace withP≤228 MUST have actual first tagged212West211
while Upper and the six Core stones remain unchanged. This is a real
route restriction, not a route premise in Lower228.
`North211Tight22812.upper_two` then proves Upper energy EXACTLY2: G≥8
plusS2/Right4, or G7-survivor plusS2/Right5, exhausts the available budget.
`NorthUpperTwoConsumed12` also proves all five original Upper identities
consumed: any one survivor would cost at least its initial debt8>2.
These roots all passed pinned kernel and independent replay. They narrow
the unresolved229 step to the actual earlyS211 support cycle.

The1-1 arrival lemmas still explicitly require zeroRest andstationary321;
`CoreStart11` does not derive stationary321 on its own. A separate
canonical tight325 mass-conservation proof is being developed to supply it.

Three bounded diagnostic replays are preserved with their exact scope.
The H7 ghost queue has57push/137moves/E4/11holes left; H8 retains237 but
still attainsE4 in67/161 with10holes left (also fresh Lean trace).
After zero186North160, a CUSTOM Upper5 queue has37/94/E2/13holes left.
Thus the missing price cannot be assigned to either isolated Upper or
Upper+212+238(+237). Core210 and the true player support components matter.
The corner320 queues fail at supports214/294; neither is a legal Goal path.


## Canonical tight325 survivor identities, now proved

`TightSurvivors11.stationary_zero_survivors` is universal for the ORIGINAL
canonical completing trace withP≤325. Upper6 and Left4 cannot pay the
initial debt of any surviving negative-value token; Rest0 forbids all
seven negative Rest survivors. Thus fifteen negative identities consume.
`LeftSix317Canonical11` forces original317 to move; Rest0 then forces it
to consume as well. The final boulder count is exactly2 (18−16holes).
Only original315 and321 remain available, each with at most one survivor.
Both therefore survive. Their initial value0 and Rest0 force both own-push
counts to0. This supplies stationary321 to the arrival proof without the
false inference Rest0⇒stationary321. The canonical partial321West probe
still stands: it has no Goal and does not meet this theorem's hypotheses.

`Upper216Eight11.reserve_eight` excludes the first216East branch under
Upper6:216E,217E,218E cost6 and a remaining193/219 pair requires2. Two
manual local footprints suffice. `LeftSplit11.six_of_split` proves Left≥6
when two paid West events have produced the split185/211 parking. It is
conditional on that actual prefix; the fixed-phase identity bridge remains
in progress. Both roots passed kernel and independent replay.

## First187 movement and the original Upper budget

`Upper187FirstGeometry12` has exactly six manually chosen zero-event words:
[108,158/132/133,159,186/160,187]. Their player regions are the old six UA
regions with187 removed. All other owned events are either positive-price
heads, one of four existing two-token tickets, or187North.187South is
impossible while these words and their outside component persist.

`Upper187FirstNorth12.first_north_four` proves an actual FIRST movement of
original187 to161 costs Upper≥4, even after arbitrary other Upper moves.
Original187 pays2; if the total were below4, the disjoint other four
identities would have budget<2. Any earlier positive head or two-token
ticket contradicts that; otherwise the firstNorth maps one of the six
words into the old UA certificate with future2.
`Upper187Quiet12.prefix_good` packages that zero-word argument. Its
`first_south_others_two` shows the first187South requires the other four
identities to spend≥2. Therefore with Upper≤2 the original187's WHOLE
energy is0 (`south_original_energy_zero`), excluding a later paid North
reset. All three roots passed pinned kernel and leanchecker.


## Two genuine canonical support/arrival necessities

`CanonicalArrival18711.canonical` now composes the checked CoreStart,
LowerElevator, and Shaft187 lemmas with TightSurvivors. For EVERY original
canonical completing1-1 trace withP≤325 it extracts an ACTUAL213North187
push owned by original Rest, retaining187/266 after it. The Arrival packet
contains canonical prefix and actual suffix logs, exact dirs/outcomes and
push/move decompositions. There are no unproved closed/321 hypotheses in
the public canonical theorem. This does not yet forbid that arrival: the
next capacity argument must control Upper188 and prior291 parking.

For1-2, `NorthUpperRigidity22812.canonical_upper_two_and_187_zero` has no
route or Upper assumptions: ANY originalafterN Goal withP≤228 has Upper2
and original187 energy0. `Upper187ForcedSouth12` extracts its actual first
187South213. `Zero213West12` forces the next owned event to213West212
and proves the required support is214. Composing the actual prefixes,
`NorthSupport21422812.canonical_support214` proves every such canonical
completion reaches player214 while the ORIGINAL187 identity is at213,
then pushes it West. These are original traces and original identities,
not a proxy corral start. All roots passed kernel/replay.

`Park317Trade12` adds a separate ten-phase symbolic bottleneck. With317
parked, a current token at345/319 fromhero318 either costs≥4 or survives
with cost≥2. The144 nonempty phase/source/direction checks have14 explicit
shift targets; walk closure is analytic. The foreign317 token has exactly
zero energy, proved and explicitly subtracted. `Park317Cash12.group_five`
therefore prices an actual318West317 plus the independent current token
at≥5 (head3 +currentfuture2), includingcurrent293/292/291 via DeadCorridor.
The old cash branch counted only head3; its omitted current-token price
can now be restored without counting Bottom2 twice. Integration into the
NorthJ alternatives remains in progress. Both roots passed fresh kernel
and leanchecker.


## Tight228 exact ledgers and the omitted parking charge

`After238210Park12` and `After210236Park12` replace the weak3-with-survivor
leaf by group≥4 (the actual park leaf is≥5). `AfterJParkRecursive12`,
`AfterJParkDeep12`, and `NorthJParkEight12.firstJ_eight` propagate this to
unconditionalG≥8 after either original firstJ event. No Upper assumptions
were added. The old conditional G7-survivor proof remains historical.

`NorthTight22812.canonical_ledgers` now proves for EVERY originalafterN
Goal withP≤228: P=228, Upper2, G8, S2, Right4, all thirteen Left tokens
consumed, original187 energy0. The survivor alternative is impossible: it
would require Right5 on top of Left12. This is still a restriction on a
hypothetical228 completion, not universal229.

Two subsequent support cuts are independently checked.
`After264Pre18712` has five prescribed currentT footprints; walking BFS
was used ONLY for static cells with each fixed footprint. Before187South,
zero currentT moves stay inside these five words; all exits are Core2,
187North2,187South0, or318West3. `After264Pre187Bound12` hands187South to
`Pocket290Gate12` and proves Corefuture≥2 OR Bottomfuture≥5 under187zero.
The Bottom branch explicitly uses currentT's independentfuture2.
`LowCoreGate12` generalizes the postSouth separator to six prescribed Core
words (without requiring S211). The only zero Core transition is237East238
between two words; the player still cannot reach214 for free. It proves
future Core≥2 under original187zero. These are actual arbitraryReached
continuation lemmas; chronology activation in every original branch is
still in progress.

For1-1, `Gate265Transport11` colors the original top10 and lower8 stones.
Before the first entry into265, colors cannot cross and the lower region
contains no original holes, so ALL8 lower identities survive there. Goal
allows only2 final boulders, hence every completing original trace has a
first gateway event. Only four entry directions matter. The16 direction
checks use actual pushTargets, including rolling. This proves chronology,
not the later325 contradiction. `FirstRest18711` separately extracts the
first ownedRest213North187 event.
`Later216Eight11` extends Upper2168 to arbitrary later owned216East while
original191 is stationary. `Arrival187Left21211` prices the two-token
187/212 separator; under remainingRest187energy0 it reserves an additional
Left212future2. `Left188Pocket11` supplies the separate three-word left
pocket capacity cut. All stated roots passed kernel/replay.


## Equality325 forces one particular original owner

The first Left186/212 West event leaves one of two two-token corrals:
[185,212] or [186,211]. Each has no owned move before its next paid West
head. `LeftQuietIdentity11` proves this for actual legal histories, so a
current position cannot silently be assigned to a different original token.
If the second West event uses the other original owner, the split185/211
corral reserves an additional2, on top of the two independent head prices2:
Left≥6. Hence at tight Left4 BOTH heads belong to one original identity.
`LeftSameActor11` is the global canonical count/energy wrapper, freshly
compiled and replayed; it is not a chosen order assumption.

The original186-paid alternative is now impossible. `Left212History11`
uses the first ANY265 boundary, growing-corral top-color retention and a
four-cell cheap212 word to show: before the first Rest213North187, a cheap
original212 is still exactly212. This includes a proof that it could not
have made its own earlier213North event. After the actual Rest arrival,
the two-token separator187/212 requires future original212 energy≥2 under
Rest0. Meanwhile Left4 minus original186≥4 forces original212 total0.
`Left186Excluded11` joins these actual prefixes/suffixes and rules out the
branch. Remaining325 case: original186 energy0, original212 energy4.

`Gate191216Eight11` independently forbids parking an Upper-owned token216
while original191 has never moved, even without assuming a216East head.
`Inward191Eight11` turns the first inward138 gate through164/190 into that
parking obstruction, with a three-to-two-token corral refinement. The
other gate can be dropped from the locks after164; no false stationarity
assumption about it is needed.

## Tight228: keep the price discarded by old numerical callers

`AfterJTightCash12` removes actual first318West and265South, and first291West
for kind0, whenever remaining group energy≤6: their existing independent
prices are≥7. `NorthJTightCash12` activates this at every actual original
firstJ210South/238South cut underP≤228 using canonicalG8 minus the head2.
The filter retains the actual before/head/after logs, phase locks, selected
original-group ownership, and the fixed ordinary subgroup. It adds no
external energy hypothesis to the canonical caller.

`SidecarCriticalFixed12` uses a useful exactness observation: a selected
group with the SAME endpoint group, zero owned slack, and unchanged length
has no absorption credits, hence no owned pushes. Thus the6 already paid
by238South264(2) and264South290(4) forces Core quietness both before and
between the events. `North238CashNo26412` derives these quiet prefixes
inside the actual event extraction. Its postcritical tail costs either
Core≥2 or Bottom≥5. Both contradict tightG8 after the already booked
prices, with disjoint-group accounting; this excludes that actual branch,
not every228 completion.

A tempting further shortcut was rejected before incorporation: "singleton
289 always costs≥2" is false because actual289East290 has zero scalar
slack. The failed FarRing4/Sidecar6 reasoning is NOT a theorem. The checked
`Far289ZeroPrice12.east_is_zero` records the local counterexample. Existing
SidecarCritical results are unaffected and never used that hypothesis.

Map names must remain explicit in transfer reasoning: a custom soko1-2
Upper diagnostic involving186North160 does NOT transfer to soko1-1.
On soko1-1 cell160 is not floor and186North has no target. A temporary
verbal task suggestion mixed these maps; it introduced no Lean statement
or proof dependency. The surviving1-1 original186 zero-word must use its
actual legal East branch instead.


## The corrected foreign211 separator, now kernel checked

The failed singleton289 ticket ignored its free East escape. Retain211
instead. Width26 gives the two support cells236=(2,9),288=(2,11).
In the Corner footprint210/211/237/262/289, support236 is enclosed by
210/237/262 and a wall; support288 is enclosed by262/289 and two walls.
The diagonal corner rule is included in the checked closure. Free210North
and237East require236; free262North and289East require288;237North is
blocked by211. Every actual exit therefore pays≥2 to the selected
Core=[210,237,262,289]. Foreign211 is a blocker, not a payer.

`S211FarFour12` books263West2 plus that independent Cornerfuture2;
210South2 activates the old Residualcredit3;237West freezes a pair;
289West already costs5. Thus FarCore requires≥4. `S211SidecarSix12`
books290West2+Far4, or210South2+Residual5. Three single-phase geometric
certificates suffice. These are actual arbitrary-reached continuation
lemmas, checked in pinned normal Lean and leanchecker. Their finite
checks are local walk/push closure, never a search of global states.

`S211SidecarCut12` activates the blocker in the real cash history:
oldSidecar4 plus the291West head2 saturates a≤6 remainder, so the fixed
Core prefix has zero slack and no absorption, hence no owned pushes.
The existing stationary211 lemma then retains211 without assuming that
Senergy2 itself means stationarity. The stronger tail6 plus that same
head2 costs8, a contradiction. `North238SidecarImpossible12` derives all
cash/core/211 premises from the original first238South packet under228.
No universal229 has yet been inferred: ordinary4 cases remain.

## The325 ordering cycle, now closed

`RightEarlyWest11` proves a canonical completing trace with Upper<8 and
Rest<2 must move the original191 via190West189 before touching137 or139.
Five explicitly prescribed words track the two original right identities;
190East191 reset is permitted, and the refinement tracks its mate rather
than postulating it. Inward gates retain owned191/193 and force the
RightTriple191/193/216 future8. Current193 stays untouched in the upper
component (`CorralQuietCell11`), so no original191 stationarity hypothesis
is smuggled into the reset case.

With original186 energy0, the independent three-pattern186/188 word and
physical frozen-pair cuts force an EARLIER original188189East190 event
before that190West189. `Row19019111` excludes the postEast190/191 pair while
both original gates137/139 are still stationary. `Cycle32511.impossible` now joins these ACTUAL prefixes. At the earlier
188189East190 head, original191 is either already190 (occupied-target
contradiction) or191 (the post-head190/191 frozen separator is impossible
while both gates remain stationary). The cycle, `Lower326` and
`Interval11_326` all passed parent normal kernel and independent leanchecker
with exactly the existing axiom allowlist. The universal current interval is
326..342; no optimality of342 is claimed.


## Two prescribed upper-schedule failures, with exact cut positions

`replay_park_reorder_failures.py` preserves two explicit original-start
replays. It asserts the expected failure; exit0 is the diagnostic's own
success, NOT a successful winning path or a lower-bound certificate.

Deleting only original321East from the checked342 schedule reaches112
legal pushes, then original266 at267 cannot be pushed West: support268 is
outside the player's component. The parking train then has137 consumed,
139at292,212at293,293at294,266at267,268at270,321at321. The scalar ledgers
lose this availability constraint; a token that is affordable in isolation
cannot necessarily receive its next initiating push. This refutes only
that specific341 schedule. Other341 plans remain possible.

A second explicit233 proposal moves original192189South215West214West213
West212 before the Upper108/186 deliveries to avoid an187 reset. It fails
already after20 pushes: support163 for189South is inaccessible fromplayer132.
This is a concrete chronology obstruction, not a universal233 exclusion.
Only walking connections use BFS; exactly two prescribed push schedules are
replayed and no boulder-configuration search is performed.


## Universal327 and229: completed canonical compositions

The consumed-energy parity is now a theorem for ANY consumed subset of an
original completing1-1 trace. The auxiliary checkerboard q uses one static
107-cell push-target check; the actual Hero315 energy is recovered only
at the consumed endpoint. The fake relaxed33East33 self-target is excluded
by actual standing/no-boulder-on-hole semantics. Genuine rolling fills are
included. Parity alone does not rule out326 because a spare can move once.

`Tight32611` obtains6/4/1; `Spare31511` and its one-push word retain315 in
314/315/316. Consequently a second physical pair away from those cells
cannot persist at Goal2. The holes-free Lower carrier gives an actual
Rest213North187 arrival without321 stationarity; quiet transport and the
same212 word now work with Rest<2. This extends the actual188/191 ordering
cycle to326. `Cycle32611`, `Lower327`, `Interval11_327` passed both parent
normal kernel and leanchecker. Current1-1 interval327..342.

For1-2, `NorthFirstJ22812.canonical` proves global coverage, including the
first265 branch via G9-or-survivor versus G8 and allLeft-consumed. The actual
first318/291 events are also eliminated. `NorthTwoJ22812` removes each other
actual first-cash case; its only three two-head packets are210→236,
210→238,238→210. `NorthTwoJPacket12` separately proves the original J4
prefix price, endpoint J permutation, actual retained phase locks and hero
component. No conditional coverage hypothesis is passed to the final root.

After those two J heads, canonicalG8 gives joint remainder≤4 and ordinary
remainder≤2 using the disjoint globalBottom2. The old strengthened Five
lemma forces ordinary≥2, so the local Bottom remainder≤2 follows by exact
partition, rather than by falsely projecting a global lower bound into an
upper bound. The two actual seven-token tail cases both contradict these
budgets. Source265 uses its future J2-or-Bottom3 trade; the B/B2 lower neck
uses five prescribed current-token phases;318West costs3; current291West
activates a residual reserve≥3. `NorthAfterTwoBudget12` and
`NorthTwoJImpossible12` close the financial and chronological composition.
`North22912`, `Lower229`, `Interval12_229` all passed parent kernel/replay.
Current1-2 interval229..235; no235 optimality claim.

`Budget32711.modes` leaves exactly(Upper,Left,Rest)=(8,4,0),(6,6,0),(6,4,2).
These newly checked alternatives are the next research cases. They do not
by themselves imply328 or329, and the original327 budget is unresolved.


## Mode327: original141 and the right pocket remove Upper8/Left4/Rest0

The old RightTripleEight bound lost a real physical obstruction. The
manually selected five footprints [191,193,216], [191,193,217],
[191,193,218], [191,193,219], [193,219] cannot all disappear when the
player is outside the two-cell194/220 pocket. Moving191West at the last
phase leaves193/219 sealing the pocket. The three priced exits instead
create the frozen192/193 pair or a dead194/220 stone. `RightPocketDead11`
proves this for every legal continuation; no original191-stationarity
assumption is used. `RightPocketNine11` therefore raises the selected
Upper reserve from8 to9 under the canonical consumed-endpoint budget.

`Mate141Before13911` proves actual original141 cannot move before original139
when Upper≤8:141West freezes139/140, while141East enters the dead142 cell.
Consequently the first original139East is impossible (it freezes140/141).
Together with the seven prescribed upper-row phases for133/135/137, this
strengthens the old shaft and right-order arguments to Upper≤8,Rest≤4.
`Zero186Strong32711` and `Budget327TwoModes11` freshly compile and replay:
Upper8/Left4/Rest0 is impossible. Only6/6/0 or6/4/2 remain at327.

A single explicit attempt at the6/6/0 case is recorded in
`replay_gate_queue_handplans.py`. After212W2,186W1,188W1,191W2,137E1S3,
the next137East from216 needs support215 outside the actual player
component. Ten earlier pushes are legal. This refutes only that prescribed
schedule; it is neither an optimality proof nor an upper witness. Moving137
into217 earlier would activate the already proved right-pocket obstruction.
Only fixed-boulder walking uses BFS in this diagnostic.


## Further exact327 and east229 restrictions

`FirstAboveMarkerPrice11` isolates the two lower marker identities instead
of charging an undifferentiated Rest group. The first actual265 entry from
above implies E264≥2 or E266≥2 or P≥335. `Mate268Before26611` rules out the
second alternative at Rest2: original268 must stay268 if its energy is0,
and original266East would freeze267/268. `FirstAboveMate11.marker264_two`
therefore identifies original264 as the actual payer. These are conditional
first-entry statements; they do not independently exclude all327 completions.

`ModeC264Mass11` proves the remaining Rest identities have energy0 once264
spends the whole Rest2. Left≤4 forces original317 to move, so its zero energy
forces absorption. The fifteen negative-debt identities are also absorbed.
Exact original mass conservation then leaves315/321 as the two survivors,
and321's zero energy makes it stationary throughout. This uses the original
18-boulder/16-hole model, not an assumed choice of spare stones.

`LeftDeadSplit11` strengthens earlier priced split bounds: the four prescribed
left footprints [185,211], [184,211], [185,210], [184,210] cannot all be absorbed
from the right component at any price. Their only continuations stay among
these shapes or enter the dead183/209 singleton. Six static separator words
suffice; the theorem has no energy or completion hypothesis. `LeftGateReserve11`
also reserves4 for the actual three-token gate [185,187,213] when original185
has less than2 remaining energy. Global activation of these local cuts is
still being formalized for the6/6/0 case.

On1-2, the old failed singleton289 claim has been replaced by a coupled
physical argument. `DiagonalDead26228912` shows the262/289 diagonal necessarily
retains both selected tokens, even if262 movesSouth or289 movesWest: either
choice freezes the pair at288. Its owned reserve is10. Consequently
`FarRingFive12` reserves5 on [210,237,263,289], without a foreign211 premise,
and `SidecarSeven12` reserves7 on [210,237,263,264,290]. Both use the existing
small head geometries and new diagonal coupling, not a global state search.

`EastTight22912.canonical_ledgers` proves necessary east-first229 budgets:
Upper2, original213energy0, Right7, moved original371energy8 (suffix372energy6),
and ALL other lower identities [210,237,238,263,265,318]energy0. It gives no
229 witness or impossibility claim. These ledgers focus the next chronological
argument instead of adding overlapping lower reservations.


## Chronology at east229: two actual original identities

`EastS238Order22912.canonical` extracts the actual first213West212 by the
original213 and proves original238 has ALREADY moved strictly earlier.
If it had not, the head would create the selected vertical pair212/238.
Its reserve2 contradicts the zero whole energy of OtherG plus original213.
This is an owned suffix bound, with current selected identities transported
through the original prefix; no zero-energy claim is projected onto an
unrelated current stone.

`Upper187StartNorth12`, `Upper187StartQuiet12` and
`Upper187StartForcedSouth12` reuse the existing six Upper geometries for an
arbitrary actually reached start containing the original Upper five. The
first187North requires4; Upper≤2 therefore forces its first pushSouth and
its whole energy0. No North-first premise remains in these new APIs.
`East187BeforeS22912.stationary_before_S` uses that four-unit North
obstruction and the actual213 collision to prove187 is stationary before
original213 moves. Its public statement has no Goal premise: an actual
prefix and suffix with whole Upper≤2 suffice.

These verified order constraints do not yet exclude east229. The next
candidate argument follows the two ways to open left support212, with
foreign Core tokens retained in the Upper separator. Static candidate
geometries and their coverage must still be kernel checked and composed.


## East231: a disjoint left-access price, not an assumed zero budget

`Foreign184UpperFour12.energy_four` handles three manually chosen current
Upper footprints retaining the foreign Core token184. Its escape heads either
activate the owned eleven-unit133/158/184 trap, or pay2 at187North and retain
a separate future2 Upper reserve. `PreAccessFour12` then follows only three
Core words (initial,263→264,237→211) together with the actual Upper five and213.
The first210North184 activates that foreign-token reserve;211North185 activates
the existing gate trap;238North freezes the physical four-stone square;213West
creates a vertical212/238 reserve2 disjoint from the still unchanged Upper2.
Every other positive Core head likewise pays2 independently of Upper2.

This proves the ten-token current group costs4 in ANY completing original
continuation from the prescribed player component. It does not assume Upper2,
Core0, S0, or P229. `East23112` combines it with original371≥8 and Right≥7 on
three DISJOINT original groups. All fresh parent kernel and leanchecker exits
are0. The whole east-first branch now needs231. The map's universal bound is
still229 because the north-first branch remains open below231.

## A reusable parity invariant on1-2, with real rolling semantics

`ConsumedParity12` uses checkerboard q and the telescoping correction
q(cell)-raw.boulder(cell). Every actual ordinary stay edge changes q by an
odd amount; real rolling fills satisfy the corresponding eighteen-credit
identity. The existing Map12 hole-order certificate excludes relaxed rolling
stay endpoints that are impossible while a hole remains. All 18 phase checks
were selectively rebuilt and replayed; this is a static phase certificate,
not a search over boulder configurations.

The theorem applies to ANY actually reached start and any absorbed selected
group whose initial correction is even. Every original Left token is compatible;
Right246/271 are not silently included. `ConsumedParity12Data` and the main
theorem both passed parent kernel and independent leanchecker.

## Stronger actual187/212 arrival reserve

`Arrival187Four11.dichotomy` needs only an actually reached state containing
187/212, player213, and eventual absorption of the current212. It proves either
current212energy≥2 or current187energy≥4. The first unavoidable head is187West
or212West. If187West occurs, it lands186; the new186/212 separator requires a
second West head before212 can disappear. The two prices are charged to the
same tracked187 identity unless212 itself pays2. Two prescribed one-phase
geometries suffice. No Goal, chosen spare, or final-capacity premise is used.
Fresh normal kernel and leanchecker exits0.

The selective cache writer now holds an exclusive nonblocking filesystem lock
for its entire compile/replay transaction. A transient overlap of two root-run
processes ended; the affected parity/arrival roots were then checked serially,
and all lane roots finished their independent replays. No overlapping cache
transaction is accepted by the updated checker script.


## North main events at230, including the formerly discarded Bottom price

`North31823112.first318_bottom_cases` exports Bottom≥7 itself, rather than
weakening it to G≥7: original318 contributes3 and the actual trapped original345
contributes4. Both Bottom identities survive. The unchanged ten-token
`PreAccessFour12` reserve4 is disjoint from these Bottom identities; their two
survivors force all Right identities to be consumed, hence Right≥8. The actual
first318West branch therefore needs231. The original old first318 theorem
and its statement were preserved unchanged.

The strengthened first265South branch has owned Lower≥9 with no survivor
exception. The old corner320 loss is repaired by retaining the OTHER Bottom
identity through just three manual265-independent phases [320,345],
[320,319], [320,293]. The free foreign292West counterexample remains valid;
it cannot remove this newly retained token. Combined with the disjoint
PreAccess4 reserve, Left≥13 follows. Consumed Left parity raises that case
to14, while surviving Left forces Right≥5; either way P≥230.

The actual291West branch similarly has prefix2 plus Ring11, hence Left≥13
and P≥230. `NorthMain23012` composes all main branches without any original
Upper orS211 assumption. `NorthSNecessary22912` then uses the separately
verified new `North187Strong22912` to eliminate Upper187North as well.
Every hypothetical original north-first P≤229 completion must now take the
actual S212West211 first exception. This is a restriction, not yet a230 lower
bound for the whole map.

`UpperBudgetParity12.two_of_lt_four` additionally shows raw Upper energy
below4 must be exactly2: all five original Upper identities are absorbed,
their compatible checkerboard correction gives even energy, and the original
Upper2 reserve still applies. Its statement needs no P budget orS211 history.


## Universal230 on1-2: the full canonical composition is checked

`North211Tight22912.canonical_ledgers` derives Upper2, G≤8 and zero original187
energy from ANY original north-first completion below230. The consumed-group
parity lemma supplies the true Left≤12 financial bound. It never substitutes
P≤228 for P≤229. `NorthFirstJ22912` reuses the old FirstJ type and obtains real
first-J coverage without all-Left-consumed: pure first265≥230 eliminates the
former G8-survivor exception directly. `NorthTwoJ22912` obtains the real second
head using explicit G≤8 critical/sidecar lemmas, again without oldP228 premises.

`NorthAfterTwoBudgetEight12` strengthens the final tail argument to a generic
G≤8 statement. After the actual two heads costJ4, the disjoint globalBottom2
leaves ordinary≤2. The ordinary local price2 then leaves Bottom≤2 as well.
The already checked physical5-phase separator excludes every such continuation.
The argument applies to the actual old FirstJ/SecondJ packet types and needs
no global P bound or assumed final choice of spare stones.

`North23012`, `Lower230`, `Interval12_230` freshly passed normal Lean4.33.1
and independent leanchecker, with the existing axiom allowlist only.
Current universal1-2 interval230..235; the upper235 witness is unchanged.
The stronger reusable `TwoJPriceNine12` also gives G≥9 for ANY actual TwoJ
packet and G≥10 when those seven identities are all absorbed, independently
of the whole push budget. This may support the next equality-case analysis.


## At327 on1-1, only Upper6/Left6/Rest0 remains

`ModeCFrontQuiet11`, `ModeCTopSplit11`, `ModeCTopFacts11` and
`ModeC212History11` extend the actual first265/firstRest187 history to Rest≤2.
The leading token cannot make its first sideways265 move: that head already
costs2, forcing the whole preceding Rest price to0. No-return then leaves that
leading token stationary, while the original neighboring264 or266 remains
in place and prevents the two support/destination cells from being clear.
No frozen-marker assumption is imported from the old Rest0 case.

The pure singleton213/239 separator now forbids early original212North without
any Rest, marker or globalP hypothesis. Combining both actual histories shows
original212 still212 at the first Rest213North187 arrival when its whole
energy is below2. The new187/212 dichotomy forces future Rest4 or Left212≥2.
Both contradict the actual ModeC budgets. The remaining exact Left4 actor
alternative has original186energy0 and is excluded by the previously verified
wide order cycle `Zero186Strong32711` (Upper≤8,Rest≤4,P≤327).

`ModeCLeft11.impossible` and `Budget327OnlyB11.mode` freshly compile and replay:
only6/6/0 remains at327. There is still no328 theorem or327 winning witness.


## ModeB: transport reserve4 and a universal row212 history

The seven prescribed pre-gate words after190West are now joined to actual
energy accounting in `AfterForwardLeftTwo11`. Left186West forces its whole
energy at least4; extra188West or190East-reset forces Upper at least8;
190North is a shaft dead end. The first inward gate move reaches138 and then
164,190,216,215,214,213. Eight manual local cuts, retaining the185/187 pair,
prove future selected energy at least4. Prefix Upper4/Left1862 leaves at most2
under ModeB and Left186≤2. This actual reached-frame theorem has no assumed
closedness, parked-token or transport premise; parent kernel+replay passed.
The thin canonical caller is being assembled; no328 lower is claimed yet.

`Row212Above11.no_north` strengthens the earlier energy-limited history:
original212 cannot initiate213North before ANY token first enters265, with
no energy, Goal, marker or total-push premise. Its thirteen singleton phases
are row8 cells209..220 and239. Away from213/239 the hero region is simply
the floor minus the tracked token, with analytic walking closure. At213/239
the existing upper-side separator closes the sole lower entrance. Thus an
east/west return to213 leaves the hero above;239North would require265 below
the boundary. Only104 local push cases use kernel decision, no global
boulder configurations or new walking tables. Parent kernel+replay passed.

The two-frame `Left184Pocket11` is also checked: [184,187,212] can quietly
change only to[184,186,212]; the first212West enters the old184/211 dead split,
and the first186West freezes184/185. No energy cap is needed. This is a
reusable obstruction for ModeB with original186 energy4, not yet its actual
canonical activation.


## Original ModeB with186≤2 is now fully excluded

`ModeBLeftTwo11.impossible` starts with the original canonical completing
trace itself, not a parked-word assumption. The real first190West cut and
the proved Lane15 tags supply prefixUpper4/original186energy2. The previously
checked seven-event continuation therefore excludes every completion with
P≤327, Upper≤6, Rest<2 and original186≤2. `only_four` combines the actual
ModeB split: ANY original completion withP≤327 now has original186energy4
and original212energy2, besides Upper6/Left6/Rest0. Both statements passed
fresh normal kernel and leanchecker. The remaining case is still unresolved.

The Lane21 extension is a local ordered-pair invariant on cells184..190,
not a global configuration graph. Its21 prescribed pair footprints allow
185West184, while a further184West needs total actor energy≥5. Every node,
label refinement and actual-prefix lift passed fresh kernel and replay.

`Post214LeftTwo11` checks only two manual four-token footprints:
[184,187,189,214] and[185,187,189,214], hero on the lower-left side. The sole
quiet owned shift is184East185. If all four selected identities are consumed,
184West183 freezes183;185East186 freezes186/187;187East188 freezes188/189.
Thus the first surviving exit must be185West184 or214East215. Importantly,
`future_two` charges its two units ONLY to the Left pair[184/185,214]: the
Upper187/189 identities stay fixed through the quiet prefix, and exact
end-group splitting assigns the paid head to Left. `future_two_perm` accepts
actual tagged groups in any order. All three theorems freshly compile and
replay. Their activation in the full remaining ModeB case is still pending;
other Upper words with original191 at190 are being handled separately.

## Stronger local1-2 reserves, without a new universal231 claim

`Post187Nine12.energy_nine` gives9 in all old ten Post187 footprints, for an
arbitrary actual reached owned group; no Goal premise is needed. A foreign
Core turn pays2 while retaining the old seven reserve. The exceptional
262South raw7 has a disjoint Upper2 reserve;161North raw8 retains the
186/212 vertical pair. No old walking matrix is enlarged.

`ResidualBoost12` reuses the six existing residual walking components and
adds three frozen-pair phases. The retained-token recurrence gives residual
credits7,7,5,10,13,0; the three terminal pair credits are4,6,9. These repair
the old loss caused by dropping the other member of a locked/diagonal pair.
They propagate to `FarRingSeven12`, `SidecarNine12`, `Quad290Nine12`.
`BottomAny12` gives a generic owned Bottom credit, and `LowerBCutSix12`
adds disjoint Bottom2 to a Core south head4 instead of counting the same
head twice. Every named module has fresh kernel and leanchecker exit0.
The stronger actual TwoJ composition is still in progress; no global231
or optimality of235 follows merely from these local lemmas.

The new three-prefix diagnostic `replay_upper_opening_parks12.py` keeps the
original canonical map. Parking original158 at133 or134 blocks support134
for108North; retaining210 while trying the Upper2 reordering blocks185 for
159North. These are exact prescribed-prefix failures, with BFS only for
walking. They refute three schedule changes, not all possible schedules,
and are neither lower theorems nor winning witnesses. The candidate opening
H10≥6/8 remains unverified; the old custom H8 energy4 counterexample remains
valid and prevents an unsupported isolated Upper strengthening.


## First265South: a forced spare, not just a larger potential

The previous Lower9 reserve plus opening4 gave Left13. Absorbed Left parity
only raised that to14, so P230 was still financially possible with Right4.
The missing fact is irreversible crowding: after265South291, the three Lower
identities cannot all be absorbed. `After265EastDead12` keeps ALL three in
the first eight old After265East footprints. Its quiet transitions stay in
those eight words. Every paid exit lands in a permanently immobile singleton:
318West317,319East320, or293East294. Thus all-three-consumed contradicts the
original legal trace, at ANY price. The preceding four-word291 corridor either
passes to these eight words or itself parks a selected stone at317.
`After265LowerSurvivor12.survives` has no Goal, P, energy or chosen-spare premise.

In parallel, optimizing only the eighteen ALREADY prescribed local footprint
credits recovers [6,7,8] at the three East starting words instead of5. The
result `After265EastSix12` contains24 explicit local shifts, with no new
walking regions or boulder-state enumeration. Its entire push predicate and
all terminal debt inequalities are independently kernel checked. The apparent
weak291South317 head7 also retains the locked317/318 pair, whose independent
terminal debt is2; discarding that pair was the old loss. Consequently
`After265PureEight12` gives future8 and `North265LowerTen12` gives Lower10
for the actual canonical first265South event.

OpeningH4 and Lower10 are disjoint, so Left≥14. The new unavoidable Lower
survivor makes Left survive, activating the already checked Right5 capacity
reserve. `North265Price23112.first265_lower_231` therefore proves
P≥212+14+5=231 for the FULL actual first265South branch. All new roots passed
fresh Lean4.33.1 and leanchecker with the old axiom allowlist. This is not yet
a universal231 bound; other North event branches still need their assembly.

`AfterTwoSeven12` and `TwoJPriceEleven12` have also now passed parent kernel
and replay. The latter gives G≥11 for any actual old FirstJ/SecondJ packet,
and G≥12 when those seven identities are absorbed. Its statement needs no
whole push budget, Upper2 assumption, or S211 history. Canonical TwoJ coverage
for the next whole-map budget is still being strengthened.


## Universal231: the actual critical packet, with arbitrary Upper history

`NorthMain23112` combines first265≥231, first318≥231 and first291≥232. The
new Deep288 two-phase separator retains the permanently immobile288 marker
and the current265→239 zero shift. It includes the real right-hand walking
detour: S213West is a zero-cost exit and keeps three DISJOINT reserves2;
263West costs2 plus the H9 future4. Thus the local future6 replaces the old
loss4 specifically behind288, without claiming a false generic H10≥6.
This propagates After29011/Ring13 and actual first291232.

The equality230 audit keeps Upper4 genuinely available. `NorthToS23012`
returns an actual S211Stage in both the earlyS and original187North cases.
The Stage records real prefix/suffix logs, S identity211, unchanged J, and
the already paid S2. `NorthFirstJ23012.after_s` obtains a real FirstJ packet
without an Upper2 or187zero assumption.

The G≤10 cash split has tail budget8. Its265 continuation costs10, its
kind0 ring costs9, the sidecar ring costs11, and318 park is separately
≥231 because it forces TWO actual Lower survivors and Right8. The remaining
ordinary second heads form the old checked SecondJ packets, whose new G11
reserve contradicts G≤10. The critical264South290 alternative is retained
explicitly in `NorthAfterFirstTen12`, rather than incorrectly excluded.

`NorthAfterFirstQuietTen12` strengthens the actual extraction by using
`EventLog.split_quiet`: no fixed Core identity has moved anywhere in the
intermediate prefix. End-tag equality alone would NOT justify this. This
real quietness preserves S211 up to the critical head. The five
`CriticalWithout18712` footprints erase187 and allow all of its movement;
they have no Upper/187/price hypothesis. Their unavoidable paid head keeps
future7:210South2+Residual7;237West freezes210/236;263West2+QuadTrap15;
265South2+After265Eight8;318West3+trapped-current debt4. Ownership includes
S211 when charging its frozen pair, so nothing is silently counted twice.

`NorthCritical23212.critical_lower232` combines actual prefix2, critical
head4 and future7 as GS≥13. Independent Upper2 gives Left≥15. Absorbed Left
rounds to16 by parity and has Right4; surviving Left has Right5. Both give
P≥232. This theorem applies to the actual critical packet with arbitrary
Upper history, covering the previously unresolved Upper4/187-reset case.

`NorthS211Impossible23012`, `NorthToS23012`, `North23112`, `Lower231` and
`Interval12_231` freshly passed normal kernel and independent leanchecker.
The original full-map universal interval is now231..235. This is an actual
new lower bound;235 remains only the checked upper witness, and the whole
three-map goal remains ACTIVE.


## First265 trade and the two original spare places

The old Lower10 estimate treated phase[320,345] as an unconditionally cheap
exit. The new eight-word Corner320Trade12 retains the disjunction: either
the needed third credit is paid, or BOTH selected stones survive. The same
19 local words in After265EastTrade12 lift this to future9, or future8 with
two survivors. No new boulder-configuration search is used. For the actual
canonical first265 packet, Lower is11, or10 with two retained identities.
Independent H4 yields Left15 in the first case and price232 by consumed
parity/capacity. In the second case Lower occupies both spare places;
Right must all be consumed and has energy8, hence price234. Thus
North265Price23212 proves the full branch232, while the map remains231..235.

NorthFirstJPark23312 retains the actual two survivor facts of the318West
exit. With actual original S2 it adds disjoint Upper2, J2, S2, Bottom7 and
Right8 to baseline212, giving233. It does not assume Upper2 equality or
zero motion of187. Extending original FirstJ coverage to the next budget
is separate work.

For1-1, the original327 budget now forces the actual first190West frame
to original186at184 and original188at186or187, with both gates untouched
and no previous Rest187. The earlier185/187 frame is excluded. The shifted
213/214 pipe proofs preserve all tracked identities and include the real
upper/lower walking detour. A proposed pure follow216 closure was false:
from custom[186188213216], player189 can walkSouth215 and push216East217.
Follow216Counter11 kernel checks that two-step custom counterexample; it
has no canonicalReach/Goal premise and proves no global bound. Only the
valid priced primary pipe closure enters the actual exclusion theorem.


## Original FirstJ with S2 costs232, without Upper rigidity

NorthFirstJPrice23212 combines the new233 parked-exit bound with actual
quiet cash extraction at budget231. Left15 would already imply232 by
consumed parity or a retained spare, so a putative231 trace hasLeft≤14.
UnconditionalUpper2 and actualS2 implyG≤10. Its actual firstJ head leaves
G-tail≤8; the real zero-Core gap is preserved. OrdinarySecondJ requiresG11,
whereas the actual critical264South packet costs232. Thus any actual
FirstJ+S2 costs232. All branches of this theorem freshly passed Lean and
leanchecker. The remaining231 investigation is FirstJ coverage before
the early318West park, not an assumed Upper2 equality.


## Universal328 from a four-frame decreasing event order

Budget327B4Activation11 starts with ANY original full-map completing trace
of at most327 pushes. Existing mode/canonicalForward lemmas force original186
at184 and original188at186/187 before190West189, with untouched137/139 and
no prior Rest213North. After that real head, original212 must be at213/214.
TaggedSix11 proves physical distinct ownership and mandatory consumption of
all six chosen identities. It supplies actualPair2/Upper4 and the budget/history
fields; no local-frame hypothesis is added to the final universal theorem.

RightParkedSix11 uses four manually selected static walking components
(Upper188at187/186 crossed with212at213/214), not a generated boulder-state
graph. At the first push of ANY selected token, all six still have their
recorded positions. Inward gates enter the checked213/214 pipe; outward gates
violate paid reserves;189West and186West freeze owned pairs or overspendUpper;
189East invokes the real Q190 reset;213West freezes the184 pocket;213South239
violates the original noRest/Above239 history. Only187West186 and214West213
remain. They map ranks[1,0,2,1] strictly down. Therefore the six cannot all
consume. RightParkedInduction11 kernel checks this finite event-order argument.

The actual canonical activation plus that induction proves
Budget327B4Impossible11.impossible, then Lower328 and Interval11_328 for
ALL original completing traces. All passed fresh Lean4.33.1 and independent
leanchecker exit0. The new interval is328..342. The other maps remain231..235
and exact141; full task is ACTIVE.


## Budget328: a new survivor alternative must not disappear

Budget32811.modes freshly kernel/replay checks the next exact budget split.
Left≤7 still consumes (initial debts22 and15), hence Left is even. Upper≤8
uses the old valid consumption lemma, leaving modes(6,4,3),(6,6,1),(8,4,1).
But budget328 allowsUpper9. Its odd energy proves that some Upper identity
survives; Left4/Rest0 then follows from total13. The initial141 debt is only7,
so simply reusing the oldUpper≤8 lemma would be invalid. This fourth
(9,4,0,survivingUpper) branch is explicitly retained. No329 bound is claimed.
