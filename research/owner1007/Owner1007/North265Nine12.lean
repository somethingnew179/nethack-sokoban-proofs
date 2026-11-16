import Owner1007.After265Seven12
import Owner1007.North265Bound12
import Owner1007.NorthGCapacity12
namespace Owner1007.North265Nine12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
theorem first265_nine_or_survivor {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
    (completed : Goal final)
    {beforeDirs beforePushes beforeMoves before middle t after afterDirs afterPushes afterMoves}
    (shape : outcomes=before ++ .push 265 (.stay 291) :: after)
    (first : Logged soko1_2.board FirstSplit12.afterN beforeDirs middle beforePushes beforeMoves before)
    (checked : step soko1_2.board middle .south=some t)
    (effect : Matches middle t (.push 265 (.stay 291)))
    (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
    (i : Fin 5) (locksInside : NorthEvents12.locks i ⊆ endGroup NorthBound12.G before) :
    9≤energy p NorthBound12.G outcomes ∨
      (8≤energy p NorthBound12.G outcomes ∧ endGroup NorthBound12.G outcomes≠[]) := by
  have initialUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
  have middleReached := NorthBound12.north_reached.append first.trace
  have middleUnique := middleReached.boulders_nodup (by decide +kernel)
  have oldInside := first.end_subset initialUnique NorthBound12.G (by decide +kernel) (by decide +kernel)
  have actualInside : NorthEvents12.locks i ⊆ middle.boulders := List.Subset.trans locksInside oldInside.2
  have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
  have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
  have nextUnique := GhostSubset.update_unique middle t (.push 265 (.stay 291)) effect nextActual
    (endGroup NorthBound12.G before) oldInside.1 oldInside.2
  have nextSubset := GhostSubset.update_subset middle t (.push 265 (.stay 291)) effect
    (endGroup NorthBound12.G before) oldInside.1 oldInside.2
  obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
  obtain ⟨dest,next,_,_,clear⟩ := (push_first_clear soko1_2.board middle 265 .south result push).2
  have destEq : dest=291 := Option.some.inj (next.symm.trans (by decide +kernel))
  have clear291 : 291 ∉ middle.boulders := by simpa only [destEq] using clear
  have small : i.val<4 := by
    by_cases yes : i.val<4
    · exact yes
    · have val : i.val=4 := by have h:=i.isLt; omega
      have same : i=(4:Fin 5) := Fin.ext val
      subst i
      exact False.elim (clear291 (actualInside (by decide +kernel)))
  let j : Fin 4 := ⟨i.val,small⟩
  have owner : 265 ∈ endGroup NorthBound12.G before := by
    apply locksInside
    have member : ∀ i : Fin 5, (265:Cell)∈NorthEvents12.locks i := by decide +kernel
    exact member i
  have nextInside := CageFour12.shifted_inside (NorthEvents12.unique i) locksInside owner
    (North265Bound12.activation i j rfl)
  have nextHero : t.state.player∈After26512.region j := by
    rw [matches_hero middle t (.push 265 (.stay 291)) effect]
    exact After26512.start_hero j
  have later := After265Seven12.energy_seven last nextReached
    (update (endGroup NorthBound12.G before) (.push 265 (.stay 291)))
    nextUnique nextSubset completed nextHero nextInside
  have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid NorthBound12.G
  change 0 ≤ ownSlack p NorthBound12.G before at prefixNN
  have price : slack p (.push 265 (.stay 291))=2 := by decide +kernel
  change 7≤energy p (update (endGroup NorthBound12.G before) (.push 265 (.stay 291))) after ∨
    (6≤energy p (update (endGroup NorthBound12.G before) (.push 265 (.stay 291))) after ∧
      endGroup (update (endGroup NorthBound12.G before) (.push 265 (.stay 291))) after≠[]) at later
  have total : energy p NorthBound12.G outcomes = ownSlack p NorthBound12.G before+2+
      energy p (update (endGroup NorthBound12.G before) (.push 265 (.stay 291))) after := by
    rw [shape,energy_at_split]
    simp only [projectedOutcome,if_pos owner,price]
  rcases later with seven|⟨six,survives⟩
  · exact Or.inl (by omega)
  · refine Or.inr ⟨by omega,?_⟩
    rw [shape,endGroup_append]
    exact survives
#print axioms first265_nine_or_survivor

theorem first265_lower227 {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
    (completed : Goal final)
    {beforeDirs beforePushes beforeMoves before middle t after afterDirs afterPushes afterMoves}
    (shape : outcomes=before ++ .push 265 (.stay 291) :: after)
    (first : Logged soko1_2.board FirstSplit12.afterN beforeDirs middle beforePushes beforeMoves before)
    (checked : step soko1_2.board middle .south=some t)
    (effect : Matches middle t (.push 265 (.stay 291)))
    (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
    (i : Fin 5) (locksInside : NorthEvents12.locks i ⊆ endGroup NorthBound12.G before) :
    227≤1+pushes := by
  have branch := first265_nine_or_survivor logged completed shape first checked effect last i locksInside
  exact NorthGCapacity12.canonical_nine_or_survivor logged completed branch
#print axioms first265_lower227

end Owner1007.North265Nine12
