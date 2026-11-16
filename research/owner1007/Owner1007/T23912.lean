import Owner1007.RingPrepared12
namespace Owner1007.T23912
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
theorem head_stage : ∀ i : Fin 4, ∀ hero∈PreCage12.ringRegion i,
 advance soko1_2.board hero .south=some 239 →
 BlockedPush soko1_2.board (PreCage12.ringLocks i) 239 .south ∨ i=3 := by decide +kernel
theorem activation : PreCage12.ringLocks 1⊆265::(PreCage12.ringLocks 3).erase 239 := by decide +kernel
theorem hero : (239:Cell)∈PreCage12.ringRegion 1 := by decide +kernel
theorem after_south239_eight
 {state middle final : State} {t : Transition}
 {beforeDirs afterDirs history : List Dir} {before after : List Outcome}
 {beforePushes beforeMoves afterPushes afterMoves past pastMoves : Nat}
 (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_2.board middle .south=some t)
 (effect : Matches middle t (.push 239 (.stay 265)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (i : Fin 4) (inside : PreCage12.ringLocks i⊆endGroup group before)
 (heroBefore : middle.player∈PreCage12.ringRegion i)
 (completed : Goal final) :
 8≤energy p group (before++(.push 239 (.stay 265))::after) := by
 have stateUnique := reached.boulders_nodup (by decide +kernel)
 have old := first.end_subset stateUnique group gUnique subset
 have middleReached := reached.append first.trace
 have middleUnique := middleReached.boulders_nodup (by decide +kernel)
 obtain ⟨_,adjacent,_⟩ := effect_push_data checked effect
 have stage : i=3 := by
   rcases head_stage i middle.player heroBefore adjacent with blocked | stage
   · exact False.elim (CageFour12.blocked_impossible (List.Subset.trans inside old.2) checked effect blocked)
   · exact stage
 subst i
 have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
 have nextUnique := GhostSubset.update_unique middle t (.push 239 (.stay 265)) effect nextActual
   (endGroup group before) old.1 old.2
 have nextSubset := GhostSubset.update_subset middle t (.push 239 (.stay 265)) effect
   (endGroup group before) old.1 old.2
 have owner : (239:Cell)∈endGroup group before := inside (by decide +kernel)
 have kept := CageFour12.shifted_inside (PreCage12.ring_unique 3) inside owner activation
 have heroNext : t.state.player∈PreCage12.ringRegion 1 := by
   rw [matches_hero middle t (.push 239 (.stay 265)) effect]
   exact hero
 have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
 have later := RingPrepared12.ring_energy_six last nextReached
   (update (endGroup group before) (.push 239 (.stay 265))) nextUnique nextSubset completed heroNext kept
 change 6≤energy p (update (endGroup group before) (.push 239 (.stay 265))) after at later
 have one : (2:Int)≤slack p (.push 239 (.stay 265)) := by decide +kernel
 have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
 change 0≤ownSlack p group before at prefixNN
 rw [energy_at_split]
 simp only [projectedOutcome,if_pos owner]
 omega
#print axioms after_south239_eight
end Owner1007.T23912

