/- Two independent ghost credits share ONE original slack budget.
Sublist transport preserves disjointness even when group7 forgets139N113. -/
import NetHack.Soko32Disjoint.ExactProjection
import NetHack.Soko32Disjoint.MapFacts
import NetHack.Soko32Penalty5.Verified
import NetHack.Sokoban.RawGhostBonus
import NetHack.Sokoban.DisjointSlack
import NetHack.Sokoban.GhostSubset
namespace NetHack.Soko32Disjoint
open NetHack.Sokoban NetHack.Soko32Penalty5
open NetHack.Sokoban.HazardPattern NetHack.Sokoban.LowerBounds
open NetHack.Sokoban.GhostProjection

def combinedValue (state : State) (second : List Cell) (credit : Nat) : Int :=
  potential.value state + Int.ofNat credit + bonus state.player second

theorem combined_step {history : List Dir} {state : State} {pushes moves : Nat}
    (reached : Trace soko3_2.board soko3_2.initial history state pushes moves)
    (first second : List Cell) (credit : Nat)
    (ticket : Ticket heroes table first state.player credit)
    (unique : (first ++ second).Nodup) (subset : first ++ second ⊆ state.boulders)
    (dir : Dir) (t : Transition) (checked : step soko3_2.board state dir = some t) :
    ∃ nextFirst nextSecond nextCredit,
      Ticket heroes table nextFirst t.state.player nextCredit ∧
      (nextFirst ++ nextSecond).Nodup ∧ nextFirst ++ nextSecond ⊆ t.state.boulders ∧
      combinedValue state second credit ≤ Int.ofNat t.pushCost + combinedValue t.state nextSecond nextCredit := by
  have pieces := List.nodup_append.mp unique
  have firstSubset : first ⊆ state.boulders := fun _ h => subset (List.mem_append_left _ h)
  have secondSubset : second ⊆ state.boulders := fun _ h => subset (List.mem_append_right _ h)
  obtain ⟨after,cost,outcome,effect,edge,afterUnique,afterSubset,_,forgotten,costEq⟩ :=
    exact_projection reached first pieces.1 firstSubset dir t checked
  have actualUnique := reached.boulders_nodup (by decide +kernel)
  have nextUnique := step_boulders_nodup _ _ _ _ actualUnique checked
  have pair := GhostSubset.pair_transport state t outcome effect nextUnique first second after unique subset forgotten
  obtain ⟨nextCredit,nextTicket,creditBound⟩ := ticket_step heroes actions table table_sound sources_inside edge ticket
  have top := RawGhostBonus.step_charge prior state actualUnique reached.holes_sublist.subset
    (trace_disjoint reached) second pieces.2.1 secondSubset dir t checked outcome effect
  change bonus state.player second ≤ slack potential (projectedOutcome second outcome) +
    bonus t.state.player (GhostPartition.update second outcome) at top
  have delta := matches_delta potential state t outcome effect
  have base := Generated.soko3_2_potential_valid.stepBound state dir t checked
  change potential.value state ≤ Int.ofNat t.pushCost + potential.value t.state at base
  have nonnegative : 0 ≤ slack potential outcome := by omega
  have separate : ∀ c ∈ first, c ∉ second := fun c one two => pieces.2.2 c one c two rfl
  have charges := DisjointSlack.sum_bound potential first second separate outcome nonnegative
  refine ⟨after,GhostPartition.update second outcome,nextCredit,nextTicket,pair.1,pair.2,?_⟩
  unfold combinedValue
  simp only [Int.ofNat_eq_natCast] at creditBound costEq delta top charges ⊢
  omega

end NetHack.Soko32Disjoint
