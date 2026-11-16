import Owner1007.RightEnergy12
import Owner1007.RightPrice4
import Owner1007.PriceTrap12Gate
import Owner1007.LockedTokens
namespace Owner1007.TokenAccounting
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection

theorem Logged.energy_mono {board initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes)
    {potential : Potential} (valid : Valid board potential) (actualUnique : initial.boulders.Nodup)
    (small large : List Cell) (smallUnique : small.Nodup) (largeUnique : large.Nodup)
    (smallActual : small ⊆ initial.boulders) (largeActual : large ⊆ initial.boulders)
    (subset : small ⊆ large) :
    energy potential small outcomes ≤ energy potential large outcomes := by
  induction logged generalizing small large with
  | nil state =>
    have bound := NonlinearFacts.weightSum_le_of_nodup_subset (fun c => -potential.boulder c)
      small large (fun c => by have h := valid.nonpositive c; omega) smallUnique subset
    simpa only [energy,ownSlack,endGroup,debtOf,Int.zero_add] using bound
  | @cons state dir t rest final pushes moves outcome outcomes checked effect tail ih =>
    have nextActual := step_boulders_nodup _ _ _ _ actualUnique checked
    have nextSmallUnique := GhostSubset.update_unique state t outcome effect nextActual small smallUnique smallActual
    have nextLargeUnique := GhostSubset.update_unique state t outcome effect nextActual large largeUnique largeActual
    have nextSmallActual := GhostSubset.update_subset state t outcome effect small smallUnique smallActual
    have nextLargeActual := GhostSubset.update_subset state t outcome effect large largeUnique largeActual
    have nextSubset := update_mono small large smallUnique subset outcome
    have one := projected_slack_mono potential small large subset outcome
      (logged_step_slack_nonnegative valid checked effect)
    have later := ih nextActual (update small outcome) (update large outcome)
      nextSmallUnique nextLargeUnique nextSmallActual nextLargeActual nextSubset
    rw [energy_cons,energy_cons]
    omega

theorem Logged.ownSlack_mono {board initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes)
    {potential : Potential} (valid : Valid board potential) (actualUnique : initial.boulders.Nodup)
    (small large : List Cell) (smallUnique : small.Nodup) (largeUnique : large.Nodup)
    (smallActual : small ⊆ initial.boulders) (largeActual : large ⊆ initial.boulders)
    (subset : small ⊆ large) :
    ownSlack potential small outcomes ≤ ownSlack potential large outcomes := by
  induction logged generalizing small large with
  | nil => exact Int.le_refl _
  | @cons state dir t rest final pushes moves outcome outcomes checked effect tail ih =>
    have nextActual := step_boulders_nodup _ _ _ _ actualUnique checked
    have nextSmallUnique := GhostSubset.update_unique state t outcome effect nextActual small smallUnique smallActual
    have nextLargeUnique := GhostSubset.update_unique state t outcome effect nextActual large largeUnique largeActual
    have nextSmallActual := GhostSubset.update_subset state t outcome effect small smallUnique smallActual
    have nextLargeActual := GhostSubset.update_subset state t outcome effect large largeUnique largeActual
    have nextSubset := update_mono small large smallUnique subset outcome
    have one := projected_slack_mono potential small large subset outcome
      (logged_step_slack_nonnegative valid checked effect)
    have later := ih nextActual (update small outcome) (update large outcome)
      nextSmallUnique nextLargeUnique nextSmallActual nextLargeActual nextSubset
    simp only [ownSlack]
    omega

theorem energy_append (potential : Potential) (group : List Cell) (before after : List Outcome) :
    energy potential group (before ++ after) =
      ownSlack potential group before + energy potential (endGroup group before) after := by
  simp only [energy,ownSlack_append,endGroup_append]
  omega

theorem prefix_slack_le_energy {board : Board} {potential : Potential}
    (valid : Valid board potential) (group : List Cell) (before after : List Outcome)
    {state final dirs pushes moves}
    (later : Logged board state dirs final pushes moves after) :
    ownSlack potential group before ≤ energy potential group (before ++ after) := by
  have nonnegative := later.energy_nonnegative valid (endGroup group before)
  rw [energy_append]
  omega

#print axioms Logged.ownSlack_mono
#print axioms prefix_slack_le_energy
#print axioms Logged.energy_mono
end Owner1007.TokenAccounting

namespace Owner1007.CageLedger12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
abbrev p := Generated.soko1_2Potential
def Upper : List Cell := [108,158,159,186,187]
theorem upper_bonus : ∀ hero ∈ [213,212,237,211,210,184,238,262,236],
    RightEnergy12.cert.bonus hero (NetHack.Sokoban.PatternCorrection.project Upper) = 2 := by decide +kernel

theorem gate_debt_credit : ∀ i, PriceTrap12Gate.credit i ≤ debtOf p (PriceTrap12Gate.locks i) := by decide +kernel

theorem gate_owned_nineteen {state final dirs pushes moves outcomes}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (group : List Cell) (groupUnique : group.Nodup) (subset : group ⊆ state.boulders)
    (hero : state.player ∈ PriceTrap12Gate.region 0)
    (inside : PriceTrap12Gate.locks 0 ⊆ group) :
    19 ≤ energy p group outcomes := by
  obtain ⟨j,_,kept,price⟩ := RightPrice4.owned_trace_price PriceTrap12Gate.closed PriceTrap12Gate.unique
    logged reached group groupUnique subset hero inside
  have debt := NonlinearFacts.weightSum_le_of_nodup_subset (fun c => -p.boulder c)
    (PriceTrap12Gate.locks j) (endGroup group outcomes)
    (fun c => by have h := Generated.soko1_2_potential_valid.nonpositive c; change p.boulder c ≤ 0 at h; omega)
    (PriceTrap12Gate.unique j) kept
  change debtOf p (PriceTrap12Gate.locks j) ≤ debtOf p (endGroup group outcomes) at debt
  have credit := gate_debt_credit j
  change 19 ≤ ownSlack p group outcomes + PriceTrap12Gate.credit j at price
  unfold energy
  omega

theorem locked_middle_square : Locked soko1_2.board [186,187,212,213] :=
  locked_of_check _ _ (by decide +kernel)
theorem locked_upper_square : Locked soko1_2.board [158,159,184,185] :=
  locked_of_check _ _ (by decide +kernel)
theorem locked_210236 : Locked soko1_2.board [210,236] :=
  locked_of_check _ _ (by decide +kernel)
theorem locked_184210 : Locked soko1_2.board [184,210] :=
  locked_of_check _ _ (by decide +kernel)
#print axioms upper_bonus
#print axioms gate_owned_nineteen
#print axioms locked_middle_square
end Owner1007.CageLedger12
