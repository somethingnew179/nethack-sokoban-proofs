import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315
open NetHack.Sokoban
open NetHack.Sokoban.HeroPhasePotential
theorem proposed_initial_value : candidateValue soko1_1.initial = 315 := by decide +kernel
theorem reverse_checked : Geometry.reverseCheck soko1_1.board = true := by decide +kernel
theorem disjoint_checked (phase : Nat) (bound : phase ≤ horizon) :
  disjointRow (soko1_1.initial.holes.drop phase) (phases.crates phase) = true := by
  have choices : phase = 0 ∨ phase = 1 ∨ phase = 2 ∨ phase = 3 ∨ phase = 4 ∨ phase = 5 ∨ phase = 6 ∨ phase = 7 ∨ phase = 8 ∨ phase = 9 ∨ phase = 10 ∨ phase = 11 ∨ phase = 12 ∨ phase = 13 ∨ phase = 14 ∨ phase = 15 ∨ phase = 16 := by change phase ≤ 16 at bound; omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

end NetHack.Soko11Hero315
