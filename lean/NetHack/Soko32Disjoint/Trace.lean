/- Whole ORIGINAL Trace transfer of the two distinct credits. No extra
player-region, monotonicity, solver or small-state Trace premise. -/
import NetHack.Soko32Disjoint.Terminal
namespace NetHack.Soko32Disjoint
open NetHack.Sokoban NetHack.Soko32Penalty5

theorem trace_bound {state final : State} {dirs : List Dir} {pushes moves : Nat}
    (tail : Trace soko3_2.board state dirs final pushes moves)
    {history : List Dir} {previousPushes previousMoves : Nat}
    (reached : Trace soko3_2.board soko3_2.initial history state previousPushes previousMoves)
    (first second : List Cell) (credit : Nat)
    (ticket : Ticket heroes table first state.player credit)
    (unique : (first ++ second).Nodup) (subset : first ++ second ⊆ state.boulders)
    (completed : Goal final) : combinedValue state second credit ≤ Int.ofNat pushes := by
  induction tail generalizing history previousPushes previousMoves first second credit with
  | nil => exact terminal_bound reached first second credit ticket unique subset completed
  | @cons state dir t rest final pushes moves head tail ih =>
    obtain ⟨nextFirst,nextSecond,nextCredit,nextTicket,nextUnique,nextSubset,bound⟩ :=
      combined_step reached first second credit ticket unique subset dir t head
    have nextReached := reached.append (Trace.cons head (Trace.nil t.state))
    have remaining := ih nextReached nextFirst nextSecond nextCredit nextTicket nextUnique nextSubset completed
    simp only [Int.ofNat_eq_natCast,Int.natCast_add] at bound remaining ⊢
    omega

end NetHack.Soko32Disjoint
