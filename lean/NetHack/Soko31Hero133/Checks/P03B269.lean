import NetHack.Soko31Hero133.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Hero133.Checks.P03B269
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 3 hero 269) = decodeDebt bits w03_269 := by
  have code : IndexedCertificateTable.get 0 rowTable (3 * stride + 269) = w03_269 := by decide +kernel
  exact packed_row rowTable horizon stride bits 3 269 w03_269 (by decide +kernel) code
theorem after_exact : (fun hero => weight 4 hero 269) = decodeDebt bits w04_269 := by
  have code : IndexedCertificateTable.get 0 rowTable (4 * stride + 269) = w04_269 := by decide +kernel
  exact packed_row rowTable horizon stride bits 4 269 w04_269 (by decide +kernel) code
theorem walk_literal : walkRow soko3_1.board (soko3_1.initial.holes.drop 3) (phases.heroes 3) 269 (decodeDebt bits w03_269) = true := by decide +kernel
theorem walk_actual : walkRow soko3_1.board (soko3_1.initial.holes.drop 3) (phases.heroes 3) 269 (fun hero => weight 3 hero 269) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko3_1.board (soko3_1.initial.holes.drop 3) (phases.heroes 3) 269 (decodeDebt bits w03_269)
    (fun landing => weight 3 269 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko3_1.board (soko3_1.initial.holes.drop 3) (phases.heroes 3) 269 (fun hero => weight 3 hero 269)
    (fun landing => weight 3 269 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko3_1.board (soko3_1.initial.holes.drop 3) 269
    (decodeDebt bits w03_269) (decodeDebt bits w04_269) = true := by decide +kernel
theorem advance_actual : advanceRow soko3_1.board (soko3_1.initial.holes.drop 3) 269
    (fun hero => weight 3 hero 269) (fun hero => weight 4 hero 269) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko31Hero133.Checks.P03B269
