/- Both selected terminal debts fit inside the debt of ALL four original
survivors, since the groups remain distinct and disjoint. -/
import NetHack.Soko32Disjoint.Step
namespace NetHack.Soko32Disjoint
open NetHack.Sokoban NetHack.Soko32Penalty5 NetHack.Sokoban.LowerBounds

theorem debt_append (first second : List Cell) : debt (first ++ second) = debt first + debt second := by
  induction first with
  | nil => simp only [List.nil_append,debt,weightSum,Int.zero_add]
  | cons c rest ih =>
    change -potential.boulder c + debt (rest ++ second) =
      (-potential.boulder c + debt rest) + debt second
    rw [ih]
    omega

theorem terminal_bound {history : List Dir} {state : State} {pushes moves : Nat}
    (reached : Trace soko3_2.board soko3_2.initial history state pushes moves)
    (first second : List Cell) (credit : Nat)
    (ticket : Ticket heroes table first state.player credit)
    (unique : (first ++ second).Nodup) (subset : first ++ second ⊆ state.boulders)
    (completed : Goal state) : combinedValue state second credit ≤ 0 := by
  have empty : state.holes = [] := completed
  have conserved := reached.conservation
  change 16 + state.holes.length = state.boulders.length + 12 at conserved
  rw [empty] at conserved
  change 16 + 0 = state.boulders.length + 12 at conserved
  have total : state.boulders.length = 4 := by omega
  have selectedLength := List.Nodup.length_le_of_subset unique subset
  have sizes : first.length + second.length ≤ 4 := by
    simpa only [List.length_append,total] using selectedLength
  have ticketBound := ticket_terminal heroes actions table table_sound ticket (by omega)
  have top := RawPatternBonus.raw_goal prior Generated.soko3_2_potential_valid state.player second
    (by change second.length ≤ 4; omega)
  change bonus state.player second ≤ debt second at top
  have debts := NonlinearFacts.weightSum_le_of_nodup_subset (fun c => -potential.boulder c)
    (first ++ second) state.boulders
    (fun c => by
      have h := Generated.soko3_2_potential_valid.nonpositive c
      change potential.boulder c ≤ 0 at h
      omega) unique subset
  change debt (first ++ second) ≤ debt state.boulders at debts
  rw [debt_append] at debts
  have finalValue : potential.value state = -debt state.boulders := by
    rw [NetHack.Soko32Penalty5.debt_neg]
    simp only [Potential.value,empty,weightSum,Int.add_zero,Int.neg_neg]
  unfold combinedValue
  rw [finalValue]
  omega

end NetHack.Soko32Disjoint
