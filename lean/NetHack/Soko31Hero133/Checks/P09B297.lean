import NetHack.Soko31Hero133.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Hero133.Checks.P09B297
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 9 hero 297) = decodeDebt bits w09_297 := by
  have code : IndexedCertificateTable.get 0 rowTable (9 * stride + 297) = w09_297 := by decide +kernel
  exact packed_row rowTable horizon stride bits 9 297 w09_297 (by decide +kernel) code
theorem after_exact : (fun hero => weight 10 hero 297) = decodeDebt bits w10_297 := by
  have code : IndexedCertificateTable.get 0 rowTable (10 * stride + 297) = w10_297 := by decide +kernel
  exact packed_row rowTable horizon stride bits 10 297 w10_297 (by decide +kernel) code
theorem walk_literal : walkRow soko3_1.board (soko3_1.initial.holes.drop 9) (phases.heroes 9) 297 (decodeDebt bits w09_297) = true := by decide +kernel
theorem walk_actual : walkRow soko3_1.board (soko3_1.initial.holes.drop 9) (phases.heroes 9) 297 (fun hero => weight 9 hero 297) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko3_1.board (soko3_1.initial.holes.drop 9) (phases.heroes 9) 297 (decodeDebt bits w09_297)
    (fun landing => weight 9 297 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko3_1.board (soko3_1.initial.holes.drop 9) (phases.heroes 9) 297 (fun hero => weight 9 hero 297)
    (fun landing => weight 9 297 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko3_1.board (soko3_1.initial.holes.drop 9) 297
    (decodeDebt bits w09_297) (decodeDebt bits w10_297) = true := by decide +kernel
theorem advance_actual : advanceRow soko3_1.board (soko3_1.initial.holes.drop 9) 297
    (fun hero => weight 9 hero 297) (fun hero => weight 10 hero 297) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko31Hero133.Checks.P09B297
