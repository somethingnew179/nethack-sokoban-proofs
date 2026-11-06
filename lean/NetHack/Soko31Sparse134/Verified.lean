import NetHack.Soko31Sparse134.Check00
import NetHack.Soko31Sparse134.Check01
import NetHack.Soko31Sparse134.Check02
import NetHack.Soko31Sparse134.Check03
import NetHack.Soko31Sparse134.Check04
import NetHack.Soko31Sparse134.Check05
import NetHack.Soko31Sparse134.Check06
import NetHack.Soko31Sparse134.Check07
import NetHack.Soko31Sparse134.Check08
import NetHack.Soko31Sparse134.Check09
import NetHack.Soko31Sparse134.Check10
import NetHack.Soko31Sparse134.Check11
import NetHack.Soko31Sparse134.Check12
import NetHack.Soko31Sparse134.Check13
import NetHack.Soko31Sparse134.Check14
import NetHack.Soko31Sparse134.Value
namespace NetHack.Soko31Sparse134
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem all_checked (phase : Nat) (active : phase < 15) : check phase = true := by
  have choices : phase = 0 ∨ phase = 1 ∨ phase = 2 ∨ phase = 3 ∨ phase = 4 ∨ phase = 5 ∨ phase = 6 ∨ phase = 7 ∨ phase = 8 ∨ phase = 9 ∨ phase = 10 ∨ phase = 11 ∨ phase = 12 ∨ phase = 13 ∨ phase = 14 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked00
  · exact checked01
  · exact checked02
  · exact checked03
  · exact checked04
  · exact checked05
  · exact checked06
  · exact checked07
  · exact checked08
  · exact checked09
  · exact checked10
  · exact checked11
  · exact checked12
  · exact checked13
  · exact checked14

/-- This strengthened base134 is used with a separately checked early2
residual. It is not itself the minimum statement. -/
theorem pushes_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko3_1.board soko3_1.initial directions final pushes moves)
    (completed : Goal final) : 134 ≤ pushes := by
  have total := trace_bound all_checked trace NetHack.Sokoban31Phases.initial_good
  rw [initial_value,value_goal_zero final completed] at total
  simp only [Int.ofNat_eq_natCast] at total
  omega
end NetHack.Soko31Sparse134
