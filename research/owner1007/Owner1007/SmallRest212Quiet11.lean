import Owner1007.Left212QuietNorth11
import Owner1007.SmallRestMarkersPrefix11
namespace Owner1007.SmallRest212Quiet11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem head_ew {state : State} {dir : Dir} {t : Transition}
 (head : step soko1_1.board state dir=some t) (metadata : t.pushSource=some 212) :
 dir=.east∨dir=.west := by
 rcases step_cases_full _ _ _ _ head with walked|pushed
 ·obtain ⟨target,_,_,_,_,shape⟩ := walked
  simp only [shape] at metadata
  contradiction
 ·obtain ⟨source,result,_,_,_,push,shape⟩ := pushed
  have same : source=212 := by simpa only [shape,Option.some.injEq] using metadata
  subst source
  have target := (pushBoulder_spec _ _ _ _ _ push).2
  have checked : allDirs.all (fun dir=>decide (pushTargets soko1_1.board 212 dir=[]∨dir=.east∨dir=.west))=true := by decide +kernel
  have choice := of_decide_eq_true (List.all_eq_true.mp checked dir (Geometry.all_directions dir))
  rcases choice with empty|east|west
  ·rw [empty] at target
   contradiction
  ·exact Or.inl east
  ·exact Or.inr west

theorem no_north {dirs state pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (prefixLog : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (suffix : Logged soko1_1.board state lastDirs final lastPushes lastMoves last) (completed : Goal final)
 (cheap : pushes+lastPushes<335)
 (restCheap : energy soko1_1.initial final UpperBudget11.Rest (outcomes++last)<2)
 (quiet : UpperQuiet11.Quiet Gate265Transport11.paid soko1_1.initial soko1_1.initial.boulders dirs state pushes moves outcomes)
 (cheap212 : energy soko1_1.initial final [212] (outcomes++last)<2) :
 PaidCount11.count FirstRest18711.paid [212] dirs outcomes=0 := by
 let full := prefixLog.append suffix
 have zeroRest := restCheap
 rcases first_cut_or_quiet (paid:=Gate265Markers11.firstPaid 212) prefixLog [212] with found|noPush
 ·obtain ⟨first⟩ := found
  have fixed := first.before.fixed (by decide :212∈([212] : List Cell)) (by intro dir;rfl)
  have tag : endGroup [212] first.beforeOutcomes=[212] := no_push_unchanged _ _ fixed
  obtain ⟨source,owner,metadata,same⟩ := first.headPaid
  change source=212 at same
  subst source
  have beforeNorth : PaidCount11.count FirstRest18711.paid [212] first.beforeDirs first.beforeOutcomes=0 := by
   have bound := TransportEvents11.count_le_ownPushes FirstRest18711.paid [212] first.beforeDirs first.beforeOutcomes
   omega
  rcases head_ew first.headChecked metadata with east|west
  ·have targets : pushTargets soko1_1.board 212 first.direction=[213] := by rw [east];decide +kernel
   have headEq := UpperHeadCases11.ordinary_effect first.headChecked first.headEffect metadata targets (by decide +kernel)
     first.before.logged.trace.holes_sublist.subset
   have effect : Matches first.middle first.actor (.push 212 (.stay 213)) := by simpa only [headEq] using first.headEffect
   let one : Logged soko1_1.board first.middle [first.direction] first.actor.state first.actor.pushCost 1 [first.headOutcome] :=
     .cons first.headChecked first.headEffect (.nil _)
   let toActor := first.before.logged.append one
   have actorTag : endGroup [212] (first.beforeOutcomes++[first.headOutcome])=[213] := by
    rw [endGroup_append,tag]
    change update [212] first.headOutcome=[213]
    rw [headEq]
    decide
   have prefixEq : (first.beforeOutcomes++[first.headOutcome])++first.afterOutcomes=outcomes := by
    simpa only [List.append_assoc,List.singleton_append] using first.outcomesEq.symm
   have markers (cell : Cell) (member : cell∈([264,266] : List Cell)) : cell∈first.actor.state.boulders := by
    have stationary := SmallRestMarkersPrefix11.stationary prefixLog suffix completed zeroRest quiet cell member
    rw [←prefixEq,ownPushes_append] at stationary
    have zero : ownPushes [cell] (first.beforeOutcomes++[first.headOutcome])=0 := by omega
    have tagCell := no_push_unchanged [cell] (first.beforeOutcomes++[first.headOutcome]) zero
    have initial : [cell]⊆soko1_1.initial.boulders := by
     simp only [List.mem_cons,List.not_mem_nil,or_false] at member
     rcases member with rfl|rfl <;> decide
    have inside := (toActor.end_subset (by decide) [cell] (by simp) initial).2
    exact inside (by rw [tagCell];simp)
   have coreInside : Left212Above11.locks 0⊆first.actor.state.boulders := by
    change ([213,264,266] : List Cell)⊆first.actor.state.boulders
    intro c member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl
    ·rw [effect.2];simp
    ·exact markers 264 (by decide)
    ·exact markers 266 (by decide)
   have hero : first.actor.state.player∈Left212Above11.region 0 := by
    have sameHero : first.actor.state.player=212 := by rw [effect.2]
    rw [sameHero]
    exact Left212Above11.start_hero
   have wholeBoundaryCount := FirstRest18711.quiet_count_zero quiet
   have concatenatedBoundary : PaidCount11.count Gate265Transport11.paid soko1_1.initial.boulders
       ((first.beforeDirs++[first.direction])++first.afterDirs)
       ((first.beforeOutcomes++[first.headOutcome])++first.afterOutcomes)=0 := by
    simpa only [List.append_assoc,List.singleton_append,←first.dirsEq,←first.outcomesEq] using wholeBoundaryCount
   rw [PaidCount11.append toActor] at concatenatedBoundary
   have tailBoundary : PaidCount11.count Gate265Transport11.paid
       (endGroup soko1_1.initial.boulders (first.beforeOutcomes++[first.headOutcome])) first.afterDirs first.afterOutcomes=0 := by omega
   have tailQuiet := QuietFromCount11.from_count first.after _ tailBoundary
   have actualUnique := (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant toActor.trace).1
   have bigUnique := (toActor.end_subset (by decide) soko1_1.initial.boulders (by decide) (by decide)).1
   have coreSubset : Left212Above11.locks 0⊆endGroup soko1_1.initial.boulders (first.beforeOutcomes++[first.headOutcome]) := by
    rw [HeroLedger.Logged.end_all toActor]
    exact coreInside
   have projected := TransportQuiet11.Quiet.project tailQuiet actualUnique bigUnique
     (by rw [HeroLedger.Logged.end_all toActor];exact List.Subset.refl _)
     (Left212Above11.locks 0) (Left212Above11.unique 0) coreSubset
   have coreNoBoundary := FirstRest18711.quiet_count_zero projected
   have slice := slice_energy_le toActor first.after suffix [212] (by decide) (by decide)
   change energy first.actor.state state (endGroup [212] (first.beforeOutcomes++[first.headOutcome])) first.afterOutcomes≤
     energy soko1_1.initial final [212] (((first.beforeOutcomes++[first.headOutcome])++first.afterOutcomes)++last) at slice
   rw [actorTag,prefixEq] at slice
   have frontCheap : energy first.actor.state state [213] first.afterOutcomes<2 := by omega
   have lastNorth := Left212Above11.no_north_of_cheap_boundary toActor.trace first.after hero coreInside frontCheap coreNoBoundary
   have headNorth : ¬PaidCount11.owned FirstRest18711.paid [212] first.direction (.push 212 (.stay 213)) := by
    change ¬(212∈([212] : List Cell)∧(212:Cell)=213∧first.direction=.north)
    rintro ⟨_,same,_⟩
    exact (by decide : (212:Cell)≠213) same
   have concatCount : PaidCount11.count FirstRest18711.paid [212]
       (first.beforeDirs++first.direction::first.afterDirs) (first.beforeOutcomes++first.headOutcome::first.afterOutcomes)=0 := by
    rw [PaidCount11.append first.before.logged]
    simp only [PaidCount11.count,beforeNorth,tag,headEq]
    rw [if_neg headNorth]
    change 0+(0+PaidCount11.count FirstRest18711.paid [213] first.afterDirs first.afterOutcomes)=0
    simpa only [Nat.zero_add] using lastNorth
   simpa only [←first.dirsEq,←first.outcomesEq] using concatCount
  ·have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.before.logged.trace
   have selected := first.before.logged.end_subset (by decide) [212] (by decide) (by decide)
   have owns : 212∈endGroup [212] first.beforeOutcomes := by rw [tag];simp
   have row := LeftStrict11.exit_row scalar rfl valid first.headChecked first.headEffect selected.1 selected.2
     ⟨212,owns,metadata,⟨Or.inr (Or.inr (Or.inr rfl)),west⟩⟩
   change 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup [212] first.beforeOutcomes) first.headOutcome+
     value first.actor.state (update (endGroup [212] first.beforeOutcomes) first.headOutcome)-value first.middle (endGroup [212] first.beforeOutcomes) at row
   have gap := logged_event_gap_le first.before.logged first.headChecked first.headEffect (first.after.append suffix) [212] (by decide) (by decide)
   have bound := Int.le_trans row gap
   change 2≤energy soko1_1.initial final [212] (first.beforeOutcomes++first.headOutcome::(first.afterOutcomes++last)) at bound
   have eqEffects : first.beforeOutcomes++first.headOutcome::(first.afterOutcomes++last)=outcomes++last := by
    calc
     _=(first.beforeOutcomes++first.headOutcome::first.afterOutcomes)++last := by simp only [List.append_assoc,List.cons_append]
     _=outcomes++last := congrArg (fun middle=>middle++last) first.outcomesEq.symm
   rw [eqEffects] at bound
   omega
 ·have fixed := noPush.fixed (by decide :212∈([212] : List Cell)) (by intro dir;rfl)
  have count := TransportEvents11.count_le_ownPushes FirstRest18711.paid [212] dirs outcomes
  omega
#print axioms head_ew
#print axioms no_north
end Owner1007.SmallRest212Quiet11
