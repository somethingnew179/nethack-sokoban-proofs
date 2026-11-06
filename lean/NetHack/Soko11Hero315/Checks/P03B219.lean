import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P03B219
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 3 hero 219) = decodeDebt bits w03_219 := by
  have code : IndexedCertificateTable.get 0 rowTable (3 * stride + 219) = w03_219 := by decide +kernel
  exact packed_row rowTable horizon stride bits 3 219 w03_219 (by decide +kernel) code
theorem after_exact : (fun hero => weight 4 hero 219) = decodeDebt bits w04_219 := by
  have code : IndexedCertificateTable.get 0 rowTable (4 * stride + 219) = w04_219 := by decide +kernel
  exact packed_row rowTable horizon stride bits 4 219 w04_219 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 3) (phases.heroes 3) 219 (decodeDebt bits w03_219) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 3) (phases.heroes 3) 219 (fun hero => weight 3 hero 219) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 3) (phases.heroes 3) 219 (decodeDebt bits w03_219)
    (fun landing => weight 3 219 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 3) (phases.heroes 3) 219 (fun hero => weight 3 hero 219)
    (fun landing => weight 3 219 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 3) 219
    (decodeDebt bits w03_219) (decodeDebt bits w04_219) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 3) 219
    (fun hero => weight 3 hero 219) (fun hero => weight 4 hero 219) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P03B219
