import Owner1007.GateMarkerSingleton11
import Owner1007.Gate265Above11Proof
namespace Owner1007.FirstAboveMarkerPrice11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.Gate265Above11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem future_obstruction {beforeDirs state beforePushes beforeMoves before dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (hero : state.player=239) (front : 265∈state.boulders)
 (zero264 : ownPushes [264] before=0) (zero266 : ownPushes [266] before=0) :
 2≤energy soko1_1.initial final [264] (before++outcomes) ∨
 2≤energy soko1_1.initial final [266] (before++outcomes) ∨335≤beforePushes+pushes := by
 let group : List Cell := [264,265,266]
 have markerZero (cell : Cell) (member : cell∈([264,266] : List Cell)) : ownPushes [cell] before=0 := by
  rcases List.mem_cons.mp member with rfl|later
  ·exact zero264
  ·have same : cell=266 := List.mem_singleton.mp later
   exact same ▸ zero266
 have markerInside (cell : Cell) (member : cell∈([264,266] : List Cell)) : cell∈state.boulders := by
  have initial : [cell]⊆soko1_1.initial.boulders := by
   rcases List.mem_cons.mp member with rfl|later
   ·decide
   ·have same : cell=266 := List.mem_singleton.mp later
    subst cell;decide
  have tag := no_push_unchanged [cell] before (markerZero cell member)
  exact (first.end_subset (by decide) [cell] (by simp) initial).2 (by rw [tag];simp)
 have inside : group⊆state.boulders := by
  intro c h
  simp only [group,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl
  ·exact markerInside 264 (by decide)
  ·exact front
  ·exact markerInside 266 (by decide)
 have good : OwnedCorral11.Good locks region state group := ⟨0,by rw [hero];decide +kernel,by decide⟩
 obtain ⟨cut⟩ := Gate265Above11.first_cut first.trace logged completed group (by decide) inside (by decide) good
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 obtain ⟨i,heroInside,locksInside⟩ := PairFirstCut11.quiet_good closed unique size cut.before valid.1 (by decide) inside (by decide) good first.trace.holes_sublist.subset
 have selected := cut.before.logged.end_subset valid.1 group (by decide) inside
 have bounded : (endGroup group cut.beforeOutcomes).length≤3 := endGroup_length_le group cut.beforeOutcomes
 obtain ⟨source,owner,metadata,shape⟩ := Gate265Above11.head_shape i heroInside locksInside selected.2 bounded cut.headChecked cut.headPaid
 let headFirst := first.append cut.before.logged
 have markerCost (cell : Cell) (member : cell∈([264,266] : List Cell))
   (metadata : cut.actor.pushSource=some cell) (pays : Triangle29111.paid cell cut.direction) :
   2≤energy soko1_1.initial final [cell] (before++outcomes) := by
  have localZero := cut.before.fixed (show cell∈group from by
    rcases List.mem_cons.mp member with rfl|later
    ·decide
    ·have same : cell=266 := List.mem_singleton.mp later
     subst cell;decide) (by
      intro dir
      rcases List.mem_cons.mp member with rfl|later
      ·exact Or.inl rfl
      ·have same : cell=266 := List.mem_singleton.mp later
       subst cell;exact Or.inr (Or.inl rfl))
  have globalZero : ownPushes [cell] (before++cut.beforeOutcomes)=0 := by
   rw [ownPushes_append,no_push_unchanged _ _ (markerZero cell member),markerZero cell member,localZero]
  have tag := no_push_unchanged [cell] (before++cut.beforeOutcomes) globalZero
  have initial : [cell]⊆soko1_1.initial.boulders := by
   rcases List.mem_cons.mp member with rfl|later
   ·decide
   ·have same : cell=266 := List.mem_singleton.mp later
    subst cell;decide
  have facts := headFirst.end_subset (by decide) [cell] (by simp) initial
  have row := Triangle29111.exit_row (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant headFirst.trace)
    facts.1 facts.2 cut.headChecked cut.headEffect (by rw [tag];simp) metadata pays
  have threshold : 2≤Triangle29111.threshold cell := by
   rcases List.mem_cons.mp member with rfl|later
   ·decide
   ·have same : cell=266 := List.mem_singleton.mp later
    subst cell;decide
  have gap := logged_event_gap_le headFirst cut.headChecked cut.headEffect cut.after [cell] (by simp) initial
  have bound := Int.le_trans threshold (Int.le_trans row gap)
  have eqEffects : (before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes=before++outcomes := by
   simp only [List.append_assoc]
   exact congrArg (List.append before) cut.outcomesEq.symm
  change 2≤energy soko1_1.initial final [cell] ((before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes) at bound
  rw [eqEffects] at bound
  exact bound
 rcases shape with ⟨rfl,west⟩|⟨rfl,east⟩|⟨rfl,south⟩
 ·exact Or.inl (markerCost 264 (by decide) metadata (Or.inl ⟨rfl,west⟩))
 ·exact Or.inr (Or.inl (markerCost 266 (by decide) metadata (Or.inr (Or.inl ⟨rfl,east⟩))))
 ·have target : pushTargets soko1_1.board 291 cut.direction=[317] := by rw [south];decide +kernel
  have eq := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) headFirst.trace.holes_sublist.subset
  have effect : Matches cut.middle cut.actor (.push 291 (.stay 317)) := by simpa only [eq] using cut.headEffect
  have deep := Deep29133511.pushes_lower headFirst (by simpa only [south] using cut.headChecked) effect cut.after completed
  have counts := cut.pushesEq
  change 335≤beforePushes+cut.beforePushes+cut.actor.pushCost+cut.afterPushes at deep
  exact Or.inr (Or.inr (by omega))
#print axioms future_obstruction
end Owner1007.FirstAboveMarkerPrice11
namespace Owner1007.FirstAboveMarkerPrice11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem above_price {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final)
 (boundary : FirstCut Gate265Transport11.paid soko1_1.initial soko1_1.initial.boulders dirs final pushes moves outcomes)
 (above : boundary.actor.pushSource=some 239 ∧ boundary.direction=.south) :
 2≤energy soko1_1.initial final [264] outcomes ∨
 2≤energy soko1_1.initial final [266] outcomes ∨335≤pushes := by
 by_cases enough264 : 2≤energy soko1_1.initial final [264] outcomes
 ·exact Or.inl enough264
 ·by_cases enough266 : 2≤energy soko1_1.initial final [266] outcomes
  ·exact Or.inr (Or.inl enough266)
  ·have cheap264 : energy soko1_1.initial final [264] outcomes<2 := by omega
   have cheap266 : energy soko1_1.initial final [266] outcomes<2 := by omega
   obtain ⟨metadata,south⟩ := above
   have target : pushTargets soko1_1.board 239 boundary.direction=[265] := by rw [south];decide +kernel
   have headEq := UpperHeadCases11.ordinary_effect boundary.headChecked boundary.headEffect metadata target
     (by decide +kernel) boundary.before.logged.trace.holes_sublist.subset
   have effect : Matches boundary.middle boundary.actor (.push 239 (.stay 265)) := by simpa only [headEq] using boundary.headEffect
   let one : Logged soko1_1.board boundary.middle [boundary.direction] boundary.actor.state boundary.actor.pushCost 1 [boundary.headOutcome] :=
     .cons boundary.headChecked boundary.headEffect (.nil _)
   let first := boundary.before.logged.append one
   have zeroAfter (cell : Cell) (member : cell∈([264,266] : List Cell)) :
     ownPushes [cell] (boundary.beforeOutcomes++[boundary.headOutcome])=0 := by
    have cap : energy soko1_1.initial final [cell] outcomes<2 := by
     rcases List.mem_cons.mp member with rfl|later
     ·exact cheap264
     ·have same : cell=266 := List.mem_singleton.mp later
      exact same ▸ cheap266
    have fixed := GateMarkerSingleton11.stationary_before logged boundary cell member cap
    have different : 239∉([cell] : List Cell) := by
     rcases List.mem_cons.mp member with rfl|later
     ·decide
     ·have same : cell=266 := List.mem_singleton.mp later
      subst cell;decide
    rw [ownPushes_append,no_push_unchanged _ _ fixed,headEq]
    simpa only [ownPushes,ownPush,if_neg different,Nat.zero_add,Nat.add_zero] using fixed
   have hero : boundary.actor.state.player=239 := by rw [effect.2]
   have front : 265∈boundary.actor.state.boulders := by rw [effect.2];simp
   have obstruction := future_obstruction first boundary.after completed hero front (zeroAfter 264 (by decide)) (zeroAfter 266 (by decide))
   have eqEffects : (boundary.beforeOutcomes++[boundary.headOutcome])++boundary.afterOutcomes=outcomes := by
    simpa only [List.append_assoc,List.singleton_append] using boundary.outcomesEq.symm
   rcases obstruction with paid264|paid266|deep
   ·change 2≤energy soko1_1.initial final [264] ((boundary.beforeOutcomes++[boundary.headOutcome])++boundary.afterOutcomes) at paid264
    rw [eqEffects] at paid264
    exact False.elim (enough264 paid264)
   ·change 2≤energy soko1_1.initial final [266] ((boundary.beforeOutcomes++[boundary.headOutcome])++boundary.afterOutcomes) at paid266
    rw [eqEffects] at paid266
    exact False.elim (enough266 paid266)
   ·have counts := boundary.pushesEq
    change 335≤boundary.beforePushes+boundary.actor.pushCost+boundary.afterPushes at deep
    exact Or.inr (Or.inr (by omega))
#print axioms above_price
end Owner1007.FirstAboveMarkerPrice11
