import Owner1007.LeftPhases32
import Owner1007.TokenPersistence
import NetHack.Soko32Disjoint.ExactProjection
import NetHack.Soko32Penalty5.Verified

namespace Owner1007.EnergyFrame32
open NetHack.Sokoban NetHack.Sokoban.LowerBounds
open NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open NetHack.Sokoban.GhostProjection Owner1007.TokenAccounting
open NetHack.Soko32Penalty5

def G : List Cell := initialGroup
def A : List Cell := LeftPhases32.phase 0
def B : List Cell := [86,113,188,211]

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem initial_partition : (G ++ (A ++ B)).Perm soko3_2.initial.boulders := by decide +kernel
theorem initial_unique : (G ++ (A ++ B)).Nodup :=
  initial_partition.nodup_iff.mpr (by decide +kernel)

theorem energy_total {dirs final pushes moves outcomes}
    (logged : Logged soko3_2.board soko3_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) :
    energy potential32 G outcomes + energy potential32 A outcomes + energy potential32 B outcomes =
      Int.ofNat pushes - 134 := by
  have actualUnique : soko3_2.initial.boulders.Nodup := by decide +kernel
  have subset : G ++ (A ++ B) ⊆ soko3_2.initial.boulders := fun _ h => initial_partition.mem_iff.mp h
  have first := logged.energy_split actualUnique potential32 G (A++B) initial_unique subset
  have second := logged.energy_split actualUnique potential32 A B
    (List.nodup_append.mp initial_unique).2.1 (fun _ h => subset (List.mem_append_right _ h))
  have same := energy_perm potential32 initial_partition outcomes
  have total := logged.all_energy potential32
  have empty : final.holes = [] := completed
  rw [Generated.soko3_2_initial_potential, empty] at total
  simp only [weightSum] at total
  omega

/-- The old certificate may forget139, but its ghost remains inside the full
persistent G. Its reserved five units therefore fit in G's OWN energy. -/
theorem ticket_energy {state final : State} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
    (logged : Logged soko3_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko3_2.board soko3_2.initial history state past pastMoves)
    (group ghost : List Cell) (credit : Nat)
    (groupUnique : group.Nodup) (groupSubset : group ⊆ state.boulders)
    (ghostUnique : ghost.Nodup) (ghostSubset : ghost ⊆ group)
    (ticket : Ticket heroes table ghost state.player credit) (completed : Goal final) :
    Int.ofNat credit ≤ energy potential32 group outcomes := by
  induction logged generalizing history past pastMoves group ghost credit with
  | nil current =>
    have conserved := reached.conservation
    have empty : current.holes = [] := completed
    change 16 + current.holes.length = current.boulders.length + 12 at conserved
    rw [empty] at conserved
    have small := List.Nodup.length_le_of_subset ghostUnique (fun c h => groupSubset (ghostSubset h))
    have terminal : ghost.length ≤ 4 := by simp only [List.length_nil] at conserved; omega
    have bound := ticket_terminal heroes actions table table_sound ticket terminal
    have debts := NonlinearFacts.weightSum_le_of_nodup_subset
      (fun cell => -potential32.boulder cell) ghost group
      (fun cell => by have h := Generated.soko3_2_potential_valid.nonpositive cell; change potential32.boulder cell ≤ 0 at h; omega)
      ghostUnique ghostSubset
    change debtOf potential32 ghost ≤ debtOf potential32 group at debts
    change Int.ofNat credit ≤ debtOf potential32 ghost at bound
    change Int.ofNat credit ≤ 0 + debtOf potential32 group
    omega
  | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
    have ghostInside : ghost ⊆ state.boulders := fun c h => groupSubset (ghostSubset h)
    obtain ⟨after, cost, other, otherEffect, edge, afterUnique, _, _, afterSublist, exactCost⟩ :=
      NetHack.Soko32Disjoint.exact_projection reached ghost ghostUnique ghostInside dir t head
    have same : other = outcome := matches_unique state t other outcome otherEffect effect
    subst other
    obtain ⟨nextCredit, nextTicket, creditBound⟩ :=
      ticket_step heroes actions table table_sound sources_inside edge ticket
    have actualUnique := reached.boulders_nodup (by decide +kernel)
    have nextUnique := step_boulders_nodup _ _ _ _ actualUnique head
    have nextGroupUnique := GhostSubset.update_unique state t outcome effect nextUnique group groupUnique groupSubset
    have nextGroupSubset := GhostSubset.update_subset state t outcome effect group groupUnique groupSubset
    have mono := update_mono ghost group ghostUnique ghostSubset outcome
    have nextGhostSubset : after ⊆ update group outcome := fun _ h => mono (afterSublist.subset h)
    have nextReached := reached.append (Trace.cons head (Trace.nil t.state))
    have restBound := ih nextReached (update group outcome) after nextCredit nextGroupUnique nextGroupSubset
      afterUnique nextGhostSubset nextTicket completed
    have nonnegative := logged_step_slack_nonnegative Generated.soko3_2_potential_valid head effect
    have charged := projected_slack_mono potential32 ghost group ghostSubset outcome nonnegative
    change Int.ofNat cost = slack potential32 (projectedOutcome ghost outcome) at exactCost
    rw [energy_cons]
    simp only [Int.ofNat_eq_natCast] at creditBound exactCost restBound ⊢
    omega

theorem group_energy_five {dirs final pushes moves outcomes}
    (logged : Logged soko3_2.board soko3_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) : 5 ≤ energy potential32 G outcomes := by
  have subset : G ⊆ soko3_2.initial.boulders :=
    fun _ h => initial_partition.mem_iff.mp (List.mem_append_left _ h)
  have bound := ticket_energy logged (Trace.nil _) G G 5
    (List.nodup_append.mp initial_unique).1 subset
    (List.nodup_append.mp initial_unique).1 (fun _ h => h) initial_ticket completed
  have five : Int.ofNat 5 = (5 : Int) := rfl
  rw [five] at bound
  exact bound

#print axioms energy_total
#print axioms group_energy_five
end Owner1007.EnergyFrame32
