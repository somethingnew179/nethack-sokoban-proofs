import Owner1007.North318BoundPlus12
import Owner1007.PreAccessFour12
import Owner1007.NorthPriceBalance12
namespace Owner1007.North31823112
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007.TokenAccounting Owner1007.OwnedEvents12 Owner1007.North318Bound12
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
abbrev H := PreAccessFour12.locks 0
theorem first318_bottom_cases {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
    {beforeDirs beforePushes beforeMoves before middle t after afterDirs afterPushes afterMoves}
    (shape : outcomes=before ++ .push 318 (.stay 317) :: after)
    (first : Logged soko1_2.board FirstSplit12.afterN beforeDirs middle beforePushes beforeMoves before)
    (checked : step soko1_2.board middle .west=some t)
    (effect : Matches middle t (.push 318 (.stay 317)))
    (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
    (i : Fin 5) (hero : middle.player∈NorthEvents12.region i)
    (locksInside : NorthEvents12.locks i ⊆ endGroup NorthBound12.G before)
    (unchanged : ∀ small : List Cell, small ⊆ NorthEvents12.J → endGroup small before=small) :
    7≤energy p NorthBound12.BottomN outcomes ∧ endGroup [318] outcomes≠[] ∧ endGroup [345] outcomes≠[] := by
  have initialUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
  have middleReached := NorthBound12.north_reached.append first.trace
  have middleUnique := middleReached.boulders_nodup (by decide +kernel)
  have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
  have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
  have prior318 := unchanged [318] (by decide +kernel)
  have fixedWhole := unchanged NorthEvents12.J (fun _ h => h)
  have splitBefore := first.end_split initialUnique NorthEvents12.J [345]
    (by decide +kernel) (by decide +kernel)
  change (endGroup NorthEvents12.J before ++ endGroup [345] before).Perm
    (endGroup NorthBound12.G before) at splitBefore
  rw [fixedWhole] at splitBefore
  have small : (endGroup [345] before).length≤1 :=
    Nat.le_trans (endGroup_length_le [345] before) (by simp)
  have prior345 := singleton_complement NorthEvents12.J (endGroup [345] before)
    (endGroup NorthBound12.G before) (NorthEvents12.current i) splitBefore
    (locksInside (current_member i)) (current_away i) small
  obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
  have member := current_for318 i middle.player hero adjacent
  have shapeNext : t.state.boulders=317::middle.boulders.erase 318 := by
    simpa only [Matches] using congrArg (fun h : Transition => h.state.boulders) effect.2
  have present : (317:Cell)∈t.state.boulders := by rw [shapeNext]; simp
  have survivesCurrent := DeadCorridor12.trapped_survives last present nextReached.holes_sublist.subset
    (NorthEvents12.current i) member
  have survives345 : endGroup [345] outcomes≠[] := by
    rw [shape,endGroup_append,prior345]
    simpa only [endGroup,update,move,if_neg (current_not318 i)] using survivesCurrent
  have survives318 := NorthBound12.after_park_survives last nextActual 318 317 present
    NorthBound12.locked317 before prior318
  have bound318 := event_energy_le Generated.soko1_2_potential_valid [318] first last (.push 318 (.stay 317))
  simp only [prior318,projectedOutcome,List.mem_cons,List.not_mem_nil,or_false,if_true] at bound318
  change slack p (.push 318 (.stay 317))≤energy p [318] (before ++ .push 318 (.stay 317) :: after) at bound318
  have price : slack p (.push 318 (.stay 317))=3 := by decide +kernel
  rw [price,←shape] at bound318
  have currentDebt := SurvivorPrefix12.current_debt_for318 i middle.player hero adjacent
  have allSurvives : endGroup [345] (before++ .push 318 (.stay 317)::after)≠[] := by
    rw [←shape]
    exact survives345
  have stronger := SurvivorPrefix12.quantitative345 first (.push 318 (.stay 317)::after)
    (NorthEvents12.current i) prior345 currentDebt allSurvives
  have bound345 : 4≤energy p [345] outcomes := by rw [shape]; exact stronger
  have bottomSplit := logged.energy_split initialUnique p [318] [345] (by decide +kernel) (by decide +kernel)
  change energy p NorthBound12.BottomN outcomes = energy p [318] outcomes + energy p [345] outcomes at bottomSplit
  exact ⟨by omega,by rw [shape]; exact survives318,survives345⟩

theorem north231 {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final)
 (branch : 7≤energy p NorthBound12.BottomN outcomes ∧endGroup [318] outcomes≠[] ∧endGroup [345] outcomes≠[]) :
 231≤1+pushes := by
 have whole := NorthWrap12.canonical_north logged
 let all := .walk 397::.push 371 (.stay 345)::outcomes
 have alive318 : endGroup [318] all≠[] := by
   change endGroup (update [318] (.push 371 (.stay 345))) outcomes≠[]
   simpa only [show update [318] (.push 371 (.stay 345))=[318] by decide +kernel] using branch.2.1
 have alive371 : endGroup [371] all≠[] := by
   change endGroup (update [371] (.push 371 (.stay 345))) outcomes≠[]
   simpa only [show update [371] (.push 371 (.stay 345))=[345] by decide +kernel] using branch.2.2
 have gone := RightConsumedEight12.right_gone_of_two_survive whole completed 318 371
   (by decide) (by decide) (by decide) alive318 alive371
 have right := RightConsumedEight12.right_eight whole completed gone
 have rightSame := NorthWrap12.energy_north Final222.R outcomes
 have unchanged : update Final222.R (.push 371 (.stay 345))=Final222.R := by decide +kernel
 rw [unchanged] at rightSame
 change energy p Final222.R all=energy p Final222.R outcomes at rightSame
 change 8≤energy p Final222.R all at right
 have four := PreAccessFour12.energy_four logged NorthBound12.north_reached H (PreAccessFour12.unique 0)
   (by decide +kernel) completed PreAccessFour12.hero371 (fun _ h=>h)
 change 4≤energy p H outcomes at four
 have split := logged.energy_split (by decide +kernel) p H NorthBound12.BottomN (by decide +kernel) (by decide +kernel)
 have mono := logged.energy_mono Generated.soko1_2_potential_valid (by decide +kernel)
   (H++NorthBound12.BottomN) NorthPriceBalance12.Left (by decide +kernel) (by decide +kernel)
   (by decide +kernel) (by decide +kernel) (by decide +kernel)
 change energy p (H++NorthBound12.BottomN) outcomes≤energy p NorthPriceBalance12.Left outcomes at mono
 have total := NorthPriceBalance12.total logged completed
 change energy p NorthPriceBalance12.Left outcomes+energy p Final222.R outcomes=Int.ofNat (1+pushes)-212 at total
 have seven : 7≤energy p NorthBound12.BottomN outcomes := branch.1
 simp only [Int.ofNat_eq_natCast] at total
 omega
theorem first318_lower231 {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
    (completed : Goal final)
    {beforeDirs beforePushes beforeMoves before middle t after afterDirs afterPushes afterMoves}
    (shape : outcomes=before ++ .push 318 (.stay 317) :: after)
    (first : Logged soko1_2.board FirstSplit12.afterN beforeDirs middle beforePushes beforeMoves before)
    (checked : step soko1_2.board middle .west=some t)
    (effect : Matches middle t (.push 318 (.stay 317)))
    (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
    (i : Fin 5) (hero : middle.player∈NorthEvents12.region i)
    (locksInside : NorthEvents12.locks i ⊆ endGroup NorthBound12.G before)
    (unchanged : ∀ small : List Cell, small ⊆ NorthEvents12.J → endGroup small before=small) :
    231≤1+pushes := by
  exact north231 logged completed (first318_bottom_cases logged shape first checked effect last i hero locksInside unchanged)

#print axioms first318_bottom_cases
#print axioms first318_lower231
end Owner1007.North31823112
