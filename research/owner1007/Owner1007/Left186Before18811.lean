import Owner1007.TightRowPairs11
import Owner1007.Left212QuietNorth11
namespace Owner1007.Left186Before18811
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem head_ew {state : State} {dir : Dir} {t : Transition} {cell : Cell}
 (member : cell∈([186,188] : List Cell))
 (head : step soko1_1.board state dir=some t) (metadata : t.pushSource=some cell) :
 dir=.east∨dir=.west := by
 rcases step_cases_full _ _ _ _ head with walked|pushed
 ·obtain ⟨target,_,_,_,_,shape⟩ := walked
  simp only [shape] at metadata
  contradiction
 ·obtain ⟨source,result,_,_,_,push,shape⟩ := pushed
  have same : source=cell := by simpa only [shape,Option.some.injEq] using metadata
  subst source
  have target := (pushBoulder_spec _ _ _ _ _ push).2
  have checked : ([186,188] : List Cell).all (fun c=>allDirs.all (fun dir=>decide (pushTargets soko1_1.board c dir=[]∨dir=.east∨dir=.west)))=true := by decide +kernel
  have choice := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked cell member) dir (Geometry.all_directions dir))
  rcases choice with empty|east|west
  ·rw [empty] at target
   contradiction
  ·exact Or.inl east
  ·exact Or.inr west

theorem stationary {dirs state pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (prefixLog : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (suffix : Logged soko1_1.board state lastDirs final lastPushes lastMoves last) (completed : Goal final)
 (cheap : pushes+lastPushes≤325)
 (zero186 : energy soko1_1.initial final [186] (outcomes++last)=0)
 (fixed188 : ownPushes [188] outcomes=0) : ownPushes [186] outcomes=0 := by
 rcases first_cut_or_quiet (paid:=Gate265Markers11.firstPaid 186) prefixLog [186] with found|quiet
 ·obtain ⟨cut⟩ := found
  have fixed := cut.before.fixed (by decide :186∈([186] : List Cell)) (by intro dir;rfl)
  have tag186 := no_push_unchanged [186] cut.beforeOutcomes fixed
  obtain ⟨source,owner,metadata,same⟩ := cut.headPaid
  change source=186 at same
  subst source
  have eqEffects : cut.beforeOutcomes++cut.headOutcome::(cut.afterOutcomes++last)=outcomes++last := by
   calc
    _=(cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes)++last := by simp only [List.append_assoc,List.cons_append]
    _=outcomes++last := congrArg (fun middle=>middle++last) cut.outcomesEq.symm
  rcases head_ew (by decide :186∈([186,188] : List Cell)) cut.headChecked metadata with east|west
  ·have target : pushTargets soko1_1.board 186 cut.direction=[187] := by rw [east];decide +kernel
   have headEq := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel)
     cut.before.logged.trace.holes_sublist.subset
   have effect : Matches cut.middle cut.actor (.push 186 (.stay 187)) := by simpa only [headEq] using cut.headEffect
   have fixed188Before : ownPushes [188] cut.beforeOutcomes=0 := by
    rw [cut.outcomesEq,ownPushes_append] at fixed188
    omega
   have tag188 := no_push_unchanged [188] cut.beforeOutcomes fixed188Before
   have selected188 := (cut.before.logged.end_subset (by decide) [188] (by decide) (by decide)).2
   have present188 : 188∈cut.middle.boulders := selected188 (by rw [tag188];simp)
   let one : Logged soko1_1.board cut.middle [cut.direction] cut.actor.state cut.actor.pushCost 1 [cut.headOutcome] :=
     .cons cut.headChecked cut.headEffect (.nil _)
   let first := cut.before.logged.append one
   let tail := cut.after.append suffix
   have countCheap : cut.beforePushes+cut.actor.pushCost+(cut.afterPushes+lastPushes)≤325 := by
    have counts:=cut.pushesEq
    omega
   have inside : TightRowPairs11.pairs 1⊆cut.actor.state.boulders := by
    change ([187,188] : List Cell)⊆cut.actor.state.boulders
    rw [effect.2]
    intro c member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    ·simp
    ·exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :188≠186)).mpr present188)
   exact False.elim (TightRowPairs11.excluded first tail completed countCheap 1 inside)
  ·have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace
   have selected := cut.before.logged.end_subset (by decide) [186] (by decide) (by decide)
   have owns : 186∈endGroup [186] cut.beforeOutcomes := by rw [tag186];simp
   have row := LeftStrict11.exit_row scalar rfl valid cut.headChecked cut.headEffect selected.1 selected.2
     ⟨186,owns,metadata,⟨Or.inr (Or.inl rfl),west⟩⟩
   change 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup [186] cut.beforeOutcomes) cut.headOutcome+
     value cut.actor.state (update (endGroup [186] cut.beforeOutcomes) cut.headOutcome)-value cut.middle (endGroup [186] cut.beforeOutcomes) at row
   have gap := logged_event_gap_le cut.before.logged cut.headChecked cut.headEffect (cut.after.append suffix) [186] (by decide) (by decide)
   have bound := Int.le_trans row gap
   change 2≤energy soko1_1.initial final [186] (cut.beforeOutcomes++cut.headOutcome::(cut.afterOutcomes++last)) at bound
   rw [eqEffects,zero186] at bound
   omega
 ·exact quiet.fixed (by decide :186∈([186] : List Cell)) (by intro dir;rfl)

theorem first188_east {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤325)
 (zero186 : energy soko1_1.initial final [186] outcomes=0)
 (cut : FirstCut (Gate265Markers11.firstPaid 188) soko1_1.initial [188] dirs final pushes moves outcomes) :
 cut.direction=.east ∧cut.headOutcome=.push 188 (.stay 189) := by
 have stationary188 := cut.before.fixed (by decide :188∈([188] : List Cell)) (by intro dir;rfl)
 let suffix := Logged.cons cut.headChecked cut.headEffect cut.after
 have counts:=cut.pushesEq
 have beforeCheap : cut.beforePushes+(cut.actor.pushCost+cut.afterPushes)≤325 := by omega
 have beforeZero : energy soko1_1.initial final [186] (cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes)=0 := by rw [←cut.outcomesEq];exact zero186
 have stationary186 := stationary cut.before.logged suffix completed beforeCheap beforeZero stationary188
 have tag186 := no_push_unchanged [186] cut.beforeOutcomes stationary186
 obtain ⟨source,owner,metadata,same⟩ := cut.headPaid
 change source=188 at same
 subst source
 rcases head_ew (by decide :188∈([186,188] : List Cell)) cut.headChecked metadata with east|west
 ·refine ⟨east,?_⟩
  exact UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata
    (by rw [east];decide +kernel) (by decide +kernel) cut.before.logged.trace.holes_sublist.subset
 ·have headEq := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata
    (show pushTargets soko1_1.board 188 cut.direction=[187] by rw [west];decide +kernel)
    (by decide +kernel) cut.before.logged.trace.holes_sublist.subset
  have effect : Matches cut.middle cut.actor (.push 188 (.stay 187)) := by simpa only [headEq] using cut.headEffect
  have present186 : 186∈cut.middle.boulders := (cut.before.logged.end_subset (by decide) [186] (by decide) (by decide)).2 (by rw [tag186];simp)
  let one : Logged soko1_1.board cut.middle [cut.direction] cut.actor.state cut.actor.pushCost 1 [cut.headOutcome] :=
    .cons cut.headChecked cut.headEffect (.nil _)
  let first := cut.before.logged.append one
  have nextCheap : cut.beforePushes+cut.actor.pushCost+cut.afterPushes≤325 := by omega
  have inside : TightRowPairs11.pairs 0⊆cut.actor.state.boulders := by
   change ([186,187] : List Cell)⊆cut.actor.state.boulders
   rw [effect.2]
   intro c member
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl
   ·exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :186≠188)).mpr present186)
   ·simp
  exact False.elim (TightRowPairs11.excluded first cut.after completed nextCheap 0 inside)
#print axioms head_ew
#print axioms stationary
#print axioms first188_east
end Owner1007.Left186Before18811
