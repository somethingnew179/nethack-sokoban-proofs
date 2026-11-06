import NetHack.Soko31Hero133.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Hero133.Checks.P11B237
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 11 hero 237) = decodeDebt bits w11_237 := by
  have code : IndexedCertificateTable.get 0 rowTable (11 * stride + 237) = w11_237 := by decide +kernel
  exact packed_row rowTable horizon stride bits 11 237 w11_237 (by decide +kernel) code
theorem after_exact : (fun hero => weight 12 hero 237) = decodeDebt bits w12_237 := by
  have code : IndexedCertificateTable.get 0 rowTable (12 * stride + 237) = w12_237 := by decide +kernel
  exact packed_row rowTable horizon stride bits 12 237 w12_237 (by decide +kernel) code
theorem walk_literal : walkRow soko3_1.board (soko3_1.initial.holes.drop 11) (phases.heroes 11) 237 (decodeDebt bits w11_237) = true := by decide +kernel
theorem walk_actual : walkRow soko3_1.board (soko3_1.initial.holes.drop 11) (phases.heroes 11) 237 (fun hero => weight 11 hero 237) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko3_1.board (soko3_1.initial.holes.drop 11) (phases.heroes 11) 237 (decodeDebt bits w11_237)
    (fun landing => weight 11 237 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko3_1.board (soko3_1.initial.holes.drop 11) (phases.heroes 11) 237 (fun hero => weight 11 hero 237)
    (fun landing => weight 11 237 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko3_1.board (soko3_1.initial.holes.drop 11) 237
    (decodeDebt bits w11_237) (decodeDebt bits w12_237) = true := by decide +kernel
theorem advance_actual : advanceRow soko3_1.board (soko3_1.initial.holes.drop 11) 237
    (fun hero => weight 11 hero 237) (fun hero => weight 12 hero 237) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko31Hero133.Checks.P11B237
