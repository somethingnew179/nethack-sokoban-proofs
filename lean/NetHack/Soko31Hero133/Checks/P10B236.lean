import NetHack.Soko31Hero133.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Hero133.Checks.P10B236
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 10 hero 236) = decodeDebt bits w10_236 := by
  have code : IndexedCertificateTable.get 0 rowTable (10 * stride + 236) = w10_236 := by decide +kernel
  exact packed_row rowTable horizon stride bits 10 236 w10_236 (by decide +kernel) code
theorem after_exact : (fun hero => weight 11 hero 236) = decodeDebt bits w11_236 := by
  have code : IndexedCertificateTable.get 0 rowTable (11 * stride + 236) = w11_236 := by decide +kernel
  exact packed_row rowTable horizon stride bits 11 236 w11_236 (by decide +kernel) code
theorem walk_literal : walkRow soko3_1.board (soko3_1.initial.holes.drop 10) (phases.heroes 10) 236 (decodeDebt bits w10_236) = true := by decide +kernel
theorem walk_actual : walkRow soko3_1.board (soko3_1.initial.holes.drop 10) (phases.heroes 10) 236 (fun hero => weight 10 hero 236) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko3_1.board (soko3_1.initial.holes.drop 10) (phases.heroes 10) 236 (decodeDebt bits w10_236)
    (fun landing => weight 10 236 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko3_1.board (soko3_1.initial.holes.drop 10) (phases.heroes 10) 236 (fun hero => weight 10 hero 236)
    (fun landing => weight 10 236 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko3_1.board (soko3_1.initial.holes.drop 10) 236
    (decodeDebt bits w10_236) (decodeDebt bits w11_236) = true := by decide +kernel
theorem advance_actual : advanceRow soko3_1.board (soko3_1.initial.holes.drop 10) 236
    (fun hero => weight 10 hero 236) (fun hero => weight 11 hero 236) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko31Hero133.Checks.P10B236
