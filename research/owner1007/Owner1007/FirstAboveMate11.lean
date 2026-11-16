import Owner1007.TightSurvivors11
import Owner1007.FirstAboveMarkerPrice11
import Owner1007.Mate268Before26611
namespace Owner1007.FirstAboveMate11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.Gate265Above11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem future_impossible {beforeDirs state beforePushes beforeMoves before dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (hero : state.player=239) (front : 265∈state.boulders)
 (zero264 : ownPushes [264] before=0) (zero266 : ownPushes [266] before=0)
 (cheap264 : energy soko1_1.initial final [264] (before++outcomes)<2)
 (cheap268 : energy soko1_1.initial final [268] (before++outcomes)<2)
 (gone266 : endGroup [266] (before++outcomes)=[]) (cheapP : beforePushes+pushes<335) : False := by
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
 ·have cost := markerCost 264 (by decide) metadata (Or.inl ⟨rfl,west⟩)
  omega
 ·have fixed := cut.before.fixed (by decide :266∈group) (by intro d;exact Or.inr (Or.inl rfl))
  have globalZero : ownPushes [266] (before++cut.beforeOutcomes)=0 := by
   rw [ownPushes_append,no_push_unchanged _ _ zero266,zero266,fixed]
  have target : pushTargets soko1_1.board 266 cut.direction=[267] := by rw [east];decide +kernel
  have headEq := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) headFirst.trace.holes_sublist.subset
  have checked : step soko1_1.board cut.middle .east=some cut.actor := by simpa only [east] using cut.headChecked
  have effect : Matches cut.middle cut.actor (.push 266 (.stay 267)) := by simpa only [headEq] using cut.headEffect
  have allEffects : (before++cut.beforeOutcomes)++.push 266 (.stay 267)::cut.afterOutcomes=before++outcomes := by
   rw [←headEq]
   simp only [List.append_assoc]
   exact congrArg (List.append before) cut.outcomesEq.symm
  have cheap : energy soko1_1.initial final [268] ((before++cut.beforeOutcomes)++.push 266 (.stay 267)::cut.afterOutcomes)<2 := by rw [allEffects];exact cheap268
  have gone : endGroup [266] ((before++cut.beforeOutcomes)++.push 266 (.stay 267)::cut.afterOutcomes)=[] := by rw [allEffects];exact gone266
  exact Mate268Before26611.no_first_east headFirst checked effect cut.after globalZero cheap gone
 ·have target : pushTargets soko1_1.board 291 cut.direction=[317] := by rw [south];decide +kernel
  have eq := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) headFirst.trace.holes_sublist.subset
  have effect : Matches cut.middle cut.actor (.push 291 (.stay 317)) := by simpa only [eq] using cut.headEffect
  have deep := Deep29133511.pushes_lower headFirst (by simpa only [south] using cut.headChecked) effect cut.after completed
  have counts := cut.pushesEq
  change 335≤beforePushes+cut.beforePushes+cut.actor.pushCost+cut.afterPushes at deep
  omega
#print axioms future_impossible
end Owner1007.FirstAboveMate11
namespace Owner1007.FirstAboveMate11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem not_above {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (boundary : FirstCut Gate265Transport11.paid soko1_1.initial soko1_1.initial.boulders dirs final pushes moves outcomes)
 (above : boundary.actor.pushSource=some 239 ∧ boundary.direction=.south)
 (cheap264 : energy soko1_1.initial final [264] outcomes<2)
 (cheap268 : energy soko1_1.initial final [268] outcomes<2)
 (gone266 : endGroup [266] outcomes=[]) (cheapP : pushes<335) : False := by
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
  have fixed : ownPushes [cell] boundary.beforeOutcomes=0 := by
   rcases List.mem_cons.mp member with rfl|later
   ·exact GateMarkerSingleton11.stationary_before logged boundary 264 (by decide) cheap264
   ·have same : cell=266 := List.mem_singleton.mp later
    subst cell
    exact Mate268Before26611.stationary_before_boundary logged boundary cheap268 gone266
  have different : 239∉([cell] : List Cell) := by
   rcases List.mem_cons.mp member with rfl|later
   ·decide
   ·have same : cell=266 := List.mem_singleton.mp later
    subst cell;decide
  rw [ownPushes_append,no_push_unchanged _ _ fixed,headEq]
  simpa only [ownPushes,ownPush,if_neg different,Nat.zero_add,Nat.add_zero] using fixed
 have hero : boundary.actor.state.player=239 := by rw [effect.2]
 have front : 265∈boundary.actor.state.boulders := by rw [effect.2];simp
 have eqEffects : (boundary.beforeOutcomes++[boundary.headOutcome])++boundary.afterOutcomes=outcomes := by
  simpa only [List.append_assoc,List.singleton_append] using boundary.outcomesEq.symm
 have c264 : energy soko1_1.initial final [264] ((boundary.beforeOutcomes++[boundary.headOutcome])++boundary.afterOutcomes)<2 := by rw [eqEffects];exact cheap264
 have c268 : energy soko1_1.initial final [268] ((boundary.beforeOutcomes++[boundary.headOutcome])++boundary.afterOutcomes)<2 := by rw [eqEffects];exact cheap268
 have gone : endGroup [266] ((boundary.beforeOutcomes++[boundary.headOutcome])++boundary.afterOutcomes)=[] := by rw [eqEffects];exact gone266
 have counts := boundary.pushesEq
 have total : boundary.beforePushes+boundary.actor.pushCost+boundary.afterPushes<335 := by omega
 exact future_impossible first boundary.after completed hero front (zeroAfter 264 (by decide)) (zeroAfter 266 (by decide)) c264 c268 gone total

theorem marker264_two {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (cheapP : pushes<335) (restCap : energy soko1_1.initial final UpperBudget11.Rest outcomes≤2)
 (boundary : FirstCut Gate265Transport11.paid soko1_1.initial soko1_1.initial.boulders dirs final pushes moves outcomes)
 (above : boundary.actor.pushSource=some 239 ∧ boundary.direction=.south) :
 2≤energy soko1_1.initial final [264] outcomes := by
 by_cases enough : 2≤energy soko1_1.initial final [264] outcomes
 ·exact enough
 ·have cheap264 : energy soko1_1.initial final [264] outcomes<2 := by omega
  rcases FirstAboveMarkerPrice11.above_price logged completed boundary above with paid264|paid266|deep
  ·exact False.elim (enough paid264)
  ·have split := HeroLedger.Logged.energy_split logged (by decide) weightAt NetHack.Soko11Hero315.holeWeight [266] [268] (by decide) (by decide)
   change energy soko1_1.initial final [266,268] outcomes=energy soko1_1.initial final [266] outcomes+energy soko1_1.initial final [268] outcomes at split
   have compare := energy_subset (Trace.nil soko1_1.initial) logged [266,268] UpperBudget11.Rest (by decide) (by decide) (by decide) (by decide) (by decide)
   have cheap268 : energy soko1_1.initial final [268] outcomes<2 := by omega
   have gone := TightSurvivors11.singleton_nil logged completed UpperBudget11.Rest (by decide) (by decide) (by decide) 2 restCap 266 (by decide) (by decide +kernel)
   exact False.elim (not_above logged completed boundary above cheap264 cheap268 gone cheapP)
  ·omega
#print axioms not_above
#print axioms marker264_two
end Owner1007.FirstAboveMate11
