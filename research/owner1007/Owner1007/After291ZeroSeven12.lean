import Owner1007.AfterJDeepLate12
namespace Owner1007.After291ZeroSeven12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential

theorem after291_seven
 {state middle final : State} {t : Transition}
 {beforeDirs afterDirs history : List Dir} {before after : List Outcome}
 {beforePushes beforeMoves afterPushes afterMoves past pastMoves : Nat}
 (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_2.board middle .west=some t)
 (effect : Matches middle t (.push 291 (.stay 290)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (unique : group.Nodup) (subset : group⊆state.boulders)
 (i : Fin 5) (inside : AfterJ12.locks 0 i⊆endGroup group before)
 (owner : (291:Cell)∈endGroup group before)
 (heroBefore : middle.player∈AfterJ12.region 0 i)
 (completed : Goal final) :
 7≤energy p group (before++(.push 291 (.stay 290))::after) := by
 have stateUnique := reached.boulders_nodup (by decide +kernel)
 have old := first.end_subset stateUnique group unique subset
 have middleReached := reached.append first.trace
 have middleUnique := middleReached.boulders_nodup (by decide +kernel)
 have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
 have nextUnique := GhostSubset.update_unique middle t (.push 291 (.stay 290)) effect nextActual
   (endGroup group before) old.1 old.2
 have nextSubset := GhostSubset.update_subset middle t (.push 291 (.stay 290)) effect
   (endGroup group before) old.1 old.2
 have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
 have hero : t.state.player=291 := matches_hero middle t (.push 291 (.stay 290)) effect
 have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
 change 0≤ownSlack p group before at prefixNN
 have price : slack p (.push 291 (.stay 290))=2 := by decide +kernel
 have later : 5≤energy p (update (endGroup group before) (.push 291 (.stay 290))) after := by
   have activation : ∀ i : Fin 5, Residual29012.locks 0⊆290::(AfterJ12.locks 0 i).erase 291 := by decide +kernel
   have kept := CageFour12.shifted_inside (AfterJ12.unique 0 i) inside owner (activation i)
   have heroNext : t.state.player∈Residual29012.region 0 := by rw [hero];decide +kernel
   have future := Residual290Any12.owned_energy_credit Residual29012.matrix last nextReached
     (update (endGroup group before) (.push 291 (.stay 290))) nextUnique nextSubset 0 heroNext kept
   change 5≤energy p (update (endGroup group before) (.push 291 (.stay 290))) after at future
   exact future
 rw [energy_at_split]
 simp only [projectedOutcome,if_pos owner,price]
 omega
#print axioms after291_seven
end Owner1007.After291ZeroSeven12

