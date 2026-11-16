import Owner1007.Cage239Six12
import Owner1007.PreRingHeads12
import Owner1007.OwnedEventsMore12
namespace Owner1007.RingCageEight12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def cageIndex (i : Fin 4) : Fin 10 := if PreCage12.ringS i=213 then 0 else 4
theorem shift_inside : ∀ i, PreCage12.ringTag i=239 → Owner1007.Cage23912.locks (cageIndex i)⊆262::(PreCage12.ringLocks i).erase 263 := by decide +kernel
theorem hero_inside : ∀ i, (263 : Cell)∈Owner1007.Cage23912.region (cageIndex i) := by decide +kernel
theorem source_inside : ∀ i, (263 : Cell)∈PreCage12.ringLocks i := by decide +kernel


theorem head_tag : ∀ i : Fin 4, ∀ hero∈PreCage12.ringRegion i,
 advance soko1_2.board hero .west=some 263 → PreCage12.ringTag i=239 := by decide +kernel

theorem actual_main_sources : ∀ i : Fin 4, ∀ hero∈PreCage12.ringRegion i,
 ∀ dir∈allDirs, ∀ source∈PreRingHeads12.sources,
 advance soko1_2.board hero dir=some source → RingCut12.paid source dir → source=263 ∨ source=290 := by decide +kernel

theorem energy_eight
    {state middle final : State} {t : Transition}
    {beforeDirs afterDirs history : List Dir} {before after : List Outcome}
    {beforePushes beforeMoves afterPushes afterMoves past pastMoves : Nat}
    (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
    (checked : step soko1_2.board middle .west=some t)
    (effect : Matches middle t (.push 263 (.stay 262)))
    (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (group : List Cell) (unique : group.Nodup) (subset : group⊆state.boulders)
    (i : Fin 4) (inside : PreCage12.ringLocks i⊆endGroup group before)
    (heroBefore : middle.player∈PreCage12.ringRegion i)
    (completed : Goal final) :
    8≤energy p group (before++(.push 263 (.stay 262))::after) := by
  have stateUnique := reached.boulders_nodup (by decide +kernel)
  have old := first.end_subset stateUnique group unique subset
  have middleReached := reached.append first.trace
  have middleUnique := middleReached.boulders_nodup (by decide +kernel)
  have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
  have nextUnique := GhostSubset.update_unique middle t (.push 263 (.stay 262)) effect nextActual
    (endGroup group before) old.1 old.2
  have nextSubset := GhostSubset.update_subset middle t (.push 263 (.stay 262)) effect
    (endGroup group before) old.1 old.2
  have owner : (263 : Cell)∈endGroup group before := inside (source_inside i)
  obtain ⟨_,adjacent,_⟩ := effect_push_data checked effect
  have tag := head_tag i middle.player heroBefore adjacent
  have kept := CageFour12.shifted_inside (PreCage12.ring_unique i) inside owner (shift_inside i tag)
  have hero : t.state.player∈Owner1007.Cage23912.region (cageIndex i) := by
    rw [matches_hero middle t (.push 263 (.stay 262)) effect]
    exact hero_inside i
  have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
  have later := Cage239Six12.energy_six last nextReached
    (update (endGroup group before) (.push 263 (.stay 262))) nextUnique nextSubset completed hero kept
  change 6≤energy p (update (endGroup group before) (.push 263 (.stay 262))) after at later
  have one : (2 : Int)≤slack p (.push 263 (.stay 262)) := by decide +kernel
  have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
  change 0≤ownSlack p group before at prefixNN
  rw [energy_at_split]
  simp only [projectedOutcome,if_pos owner]
  omega
#print axioms energy_eight
end Owner1007.RingCageEight12

