import NetHack.Soko31Hero133.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Hero133.Checks.P10B270
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 10 hero 270) = decodeDebt bits w10_270 := by
  have code : IndexedCertificateTable.get 0 rowTable (10 * stride + 270) = w10_270 := by decide +kernel
  exact packed_row rowTable horizon stride bits 10 270 w10_270 (by decide +kernel) code
theorem after_exact : (fun hero => weight 11 hero 270) = decodeDebt bits w11_270 := by
  have code : IndexedCertificateTable.get 0 rowTable (11 * stride + 270) = w11_270 := by decide +kernel
  exact packed_row rowTable horizon stride bits 11 270 w11_270 (by decide +kernel) code
theorem walk_literal : walkRow soko3_1.board (soko3_1.initial.holes.drop 10) (phases.heroes 10) 270 (decodeDebt bits w10_270) = true := by decide +kernel
theorem walk_actual : walkRow soko3_1.board (soko3_1.initial.holes.drop 10) (phases.heroes 10) 270 (fun hero => weight 10 hero 270) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko3_1.board (soko3_1.initial.holes.drop 10) (phases.heroes 10) 270 (decodeDebt bits w10_270)
    (fun landing => weight 10 270 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko3_1.board (soko3_1.initial.holes.drop 10) (phases.heroes 10) 270 (fun hero => weight 10 hero 270)
    (fun landing => weight 10 270 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko3_1.board (soko3_1.initial.holes.drop 10) 270
    (decodeDebt bits w10_270) (decodeDebt bits w11_270) = true := by decide +kernel
theorem advance_actual : advanceRow soko3_1.board (soko3_1.initial.holes.drop 10) 270
    (fun hero => weight 10 hero 270) (fun hero => weight 11 hero 270) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko31Hero133.Checks.P10B270
