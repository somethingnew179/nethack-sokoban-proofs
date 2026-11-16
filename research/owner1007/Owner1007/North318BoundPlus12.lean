import Owner1007.North318Bound12
import Owner1007.SurvivorPrefix12
import Owner1007.Final222
import Owner1007.NorthWrap12
import Owner1007.RightCapacity12
import Owner1007.RightConsumedEight12
namespace Owner1007.North318BoundPlus12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12 Owner1007.North318Bound12
abbrev p := Generated.soko1_2Potential
theorem first318_cases {dirs final pushes moves outcomes}
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
    7≤energy p NorthBound12.G outcomes ∧ endGroup [318] outcomes≠[] ∧ endGroup [345] outcomes≠[] := by
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
  have jNN := logged.energy_nonnegative Generated.soko1_2_potential_valid NorthBound12.J
  change 0≤energy p NorthBound12.J outcomes at jNN
  have gSplit := logged.energy_split initialUnique p NorthBound12.J NorthBound12.BottomN
    (by decide +kernel) (by decide +kernel)
  change energy p NorthBound12.G outcomes =
    energy p NorthBound12.J outcomes + energy p NorthBound12.BottomN outcomes at gSplit
  exact ⟨by omega,by rw [shape]; exact survives318,survives345⟩


#print axioms first318_cases

/-- The strengthened first318 reservation implies226 canonical pushes in that branch. -/
theorem north226 {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final)
 (branch : 7≤energy p NorthBound12.G outcomes ∧ endGroup [318] outcomes≠[]) :
 226≤1+pushes := by
 have whole := NorthWrap12.canonical_north logged
 let all := .walk 397 :: .push 371 (.stay 345) :: outcomes
 have perm : (update Final222.G (.push 371 (.stay 345))).Perm NorthBound12.G := by decide +kernel
 have same : energy p Final222.G all=energy p NorthBound12.G outcomes :=
   (NorthWrap12.energy_north Final222.G outcomes).trans (energy_perm p perm outcomes)
 have seven : 7≤energy p Final222.G all := by rw [same]; exact branch.1
 have survives : endGroup [318] all≠[] := by
   change endGroup (update [318] (.push 371 (.stay 345))) outcomes≠[]
   have unchanged : update [318] (.push 371 (.stay 345))=[318] := by decide +kernel
   rw [unchanged]
   exact branch.2
 have right := RightCapacity12.right_energy_five_of318survives whole completed survives
 change 5≤energy p Final222.R all at right
 have upper := Final222.upper_energy_two whole completed
 change 2≤energy p Final222.U all at upper
 have other := whole.energy_nonnegative Generated.soko1_2_potential_valid [213]
 change 0≤energy p [213] all at other
 have total := Final222.total_energy whole completed
 change energy p Final222.U all + energy p Final222.G all + energy p [213] all + energy p Final222.R all =
   Int.ofNat (1+pushes)-212 at total
 simp only [Int.ofNat_eq_natCast] at total
 omega
#print axioms north226

theorem north229 {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final)
 (branch : 7≤energy p NorthBound12.G outcomes ∧ endGroup [318] outcomes≠[] ∧ endGroup [345] outcomes≠[]) :
 229≤1+pushes := by
 have whole := NorthWrap12.canonical_north logged
 let all := .walk 397 :: .push 371 (.stay 345) :: outcomes
 have survives318 : endGroup [318] all≠[] := by
   change endGroup (update [318] (.push 371 (.stay 345))) outcomes≠[]
   have unchanged : update [318] (.push 371 (.stay 345))=[318] := by decide +kernel
   rw [unchanged]
   exact branch.2.1
 have survives371 : endGroup [371] all≠[] := by
   change endGroup (update [371] (.push 371 (.stay 345))) outcomes≠[]
   have unchanged : update [371] (.push 371 (.stay 345))=[345] := by decide +kernel
   rw [unchanged]
   exact branch.2.2
 have gone := RightConsumedEight12.right_gone_of_two_survive whole completed 318 371
   (by decide) (by decide) (by decide) survives318 survives371
 have right := RightConsumedEight12.right_eight whole completed gone
 change 8≤energy p Final222.R all at right
 have perm : (update Final222.G (.push 371 (.stay 345))).Perm NorthBound12.G := by decide +kernel
 have same : energy p Final222.G all=energy p NorthBound12.G outcomes :=
   (NorthWrap12.energy_north Final222.G outcomes).trans (energy_perm p perm outcomes)
 have seven : 7≤energy p Final222.G all := by rw [same]; exact branch.1
 have upper := Final222.upper_energy_two whole completed
 change 2≤energy p Final222.U all at upper
 have other := whole.energy_nonnegative Generated.soko1_2_potential_valid [213]
 change 0≤energy p [213] all at other
 have total := Final222.total_energy whole completed
 change energy p Final222.U all + energy p Final222.G all + energy p [213] all + energy p Final222.R all =
   Int.ofNat (1+pushes)-212 at total
 simp only [Int.ofNat_eq_natCast] at total
 omega
#print axioms north229
theorem first318_lower229 {dirs final pushes moves outcomes}
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
    229≤1+pushes := by
  exact north229 logged completed (first318_cases logged shape first checked effect last i hero locksInside unchanged)
#print axioms first318_lower229
end Owner1007.North318BoundPlus12
