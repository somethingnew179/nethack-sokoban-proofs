import NetHack.Soko31Hero133.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Hero133.Checks.P09B239
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 9 hero 239) = decodeDebt bits w09_239 := by
  have code : IndexedCertificateTable.get 0 rowTable (9 * stride + 239) = w09_239 := by decide +kernel
  exact packed_row rowTable horizon stride bits 9 239 w09_239 (by decide +kernel) code
theorem after_exact : (fun hero => weight 10 hero 239) = decodeDebt bits w10_239 := by
  have code : IndexedCertificateTable.get 0 rowTable (10 * stride + 239) = w10_239 := by decide +kernel
  exact packed_row rowTable horizon stride bits 10 239 w10_239 (by decide +kernel) code
theorem walk_literal : walkRow soko3_1.board (soko3_1.initial.holes.drop 9) (phases.heroes 9) 239 (decodeDebt bits w09_239) = true := by decide +kernel
theorem walk_actual : walkRow soko3_1.board (soko3_1.initial.holes.drop 9) (phases.heroes 9) 239 (fun hero => weight 9 hero 239) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko3_1.board (soko3_1.initial.holes.drop 9) (phases.heroes 9) 239 (decodeDebt bits w09_239)
    (fun landing => weight 9 239 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko3_1.board (soko3_1.initial.holes.drop 9) (phases.heroes 9) 239 (fun hero => weight 9 hero 239)
    (fun landing => weight 9 239 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko3_1.board (soko3_1.initial.holes.drop 9) 239
    (decodeDebt bits w09_239) (decodeDebt bits w10_239) = true := by decide +kernel
theorem advance_actual : advanceRow soko3_1.board (soko3_1.initial.holes.drop 9) 239
    (fun hero => weight 9 hero 239) (fun hero => weight 10 hero 239) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko31Hero133.Checks.P09B239
