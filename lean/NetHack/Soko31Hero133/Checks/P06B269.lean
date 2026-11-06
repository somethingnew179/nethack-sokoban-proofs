import NetHack.Soko31Hero133.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Hero133.Checks.P06B269
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 6 hero 269) = decodeDebt bits w06_269 := by
  have code : IndexedCertificateTable.get 0 rowTable (6 * stride + 269) = w06_269 := by decide +kernel
  exact packed_row rowTable horizon stride bits 6 269 w06_269 (by decide +kernel) code
theorem after_exact : (fun hero => weight 7 hero 269) = decodeDebt bits w07_269 := by
  have code : IndexedCertificateTable.get 0 rowTable (7 * stride + 269) = w07_269 := by decide +kernel
  exact packed_row rowTable horizon stride bits 7 269 w07_269 (by decide +kernel) code
theorem walk_literal : walkRow soko3_1.board (soko3_1.initial.holes.drop 6) (phases.heroes 6) 269 (decodeDebt bits w06_269) = true := by decide +kernel
theorem walk_actual : walkRow soko3_1.board (soko3_1.initial.holes.drop 6) (phases.heroes 6) 269 (fun hero => weight 6 hero 269) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko3_1.board (soko3_1.initial.holes.drop 6) (phases.heroes 6) 269 (decodeDebt bits w06_269)
    (fun landing => weight 6 269 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko3_1.board (soko3_1.initial.holes.drop 6) (phases.heroes 6) 269 (fun hero => weight 6 hero 269)
    (fun landing => weight 6 269 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko3_1.board (soko3_1.initial.holes.drop 6) 269
    (decodeDebt bits w06_269) (decodeDebt bits w07_269) = true := by decide +kernel
theorem advance_actual : advanceRow soko3_1.board (soko3_1.initial.holes.drop 6) 269
    (fun hero => weight 6 hero 269) (fun hero => weight 7 hero 269) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko31Hero133.Checks.P06B269
