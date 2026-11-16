import Owner1007.AfterJRecursive12
import Owner1007.After265PureEight12
import Owner1007.After265LowerSurvivor12
import Owner1007.Sidecar26412
import Owner1007.Residual290Any12
import Owner1007.DeadCorridor12
import Owner1007.TokenPersistence
namespace Owner1007.AfterJDeepTen12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential

theorem activation : ∀ kind : Fin 2, ∀ i : Fin 5, ∀ j : Fin 4, i.val=j.val →
 After26512.locks j⊆291::(AfterJ12.locks kind i).erase 265 := by decide +kernel

theorem after265_ten
 {state middle final : State} {t : Transition}
 {beforeDirs afterDirs history : List Dir} {before after : List Outcome}
 {beforePushes beforeMoves afterPushes afterMoves past pastMoves : Nat}
 (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_2.board middle .south=some t)
 (effect : Matches middle t (.push 265 (.stay 291)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (unique : group.Nodup) (subset : group⊆state.boulders)
 (kind : Fin 2) (i : Fin 5) (locksInside : AfterJ12.locks kind i⊆endGroup group before)
 (completed : Goal final) :
 10≤energy p group (before++(.push 265 (.stay 291))::after) := by
  have initialUnique := reached.boulders_nodup (by decide +kernel)
  have middleReached := reached.append first.trace
  have middleUnique := middleReached.boulders_nodup (by decide +kernel)
  have oldInside := first.end_subset initialUnique group unique subset
  have actualInside : AfterJ12.locks kind i ⊆ middle.boulders := List.Subset.trans locksInside oldInside.2
  have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
  have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
  have nextUnique := GhostSubset.update_unique middle t (.push 265 (.stay 291)) effect nextActual
    (endGroup group before) oldInside.1 oldInside.2
  have nextSubset := GhostSubset.update_subset middle t (.push 265 (.stay 291)) effect
    (endGroup group before) oldInside.1 oldInside.2
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
      have present : ∀ kind : Fin 2, (291:Cell)∈AfterJ12.locks kind 4 := by decide +kernel
      exact False.elim (clear291 (actualInside (present kind)))
  let j : Fin 4 := ⟨i.val,small⟩
  have owner : 265 ∈ endGroup group before := by
    apply locksInside
    have member : ∀ kind : Fin 2, ∀ i : Fin 5, (265:Cell)∈AfterJ12.locks kind i := by decide +kernel
    exact member kind i
  have nextInside := CageFour12.shifted_inside (AfterJ12.unique kind i) locksInside owner
    (activation kind i j rfl)
  have nextHero : t.state.player∈After26512.region j := by
    rw [matches_hero middle t (.push 265 (.stay 291)) effect]
    exact After26512.start_hero j
  have later := After265PureEight12.energy_eight last nextReached
    (update (endGroup group before) (.push 265 (.stay 291)))
    nextUnique nextSubset completed nextHero nextInside
  have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
  change 0 ≤ ownSlack p group before at prefixNN
  have price : slack p (.push 265 (.stay 291))=2 := by decide +kernel
  change 8 ≤ energy p (update (endGroup group before) (.push 265 (.stay 291))) after at later
  rw [energy_at_split]
  simp only [projectedOutcome,if_pos owner,price]
  omega
#print axioms after265_ten
end Owner1007.AfterJDeepTen12
