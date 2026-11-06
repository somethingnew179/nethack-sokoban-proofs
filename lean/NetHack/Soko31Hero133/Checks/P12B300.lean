import NetHack.Soko31Hero133.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Hero133.Checks.P12B300
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 12 hero 300) = decodeDebt bits w12_300 := by
  have code : IndexedCertificateTable.get 0 rowTable (12 * stride + 300) = w12_300 := by decide +kernel
  exact packed_row rowTable horizon stride bits 12 300 w12_300 (by decide +kernel) code
theorem after_exact : (fun hero => weight 13 hero 300) = decodeDebt bits w13_300 := by
  have code : IndexedCertificateTable.get 0 rowTable (13 * stride + 300) = w13_300 := by decide +kernel
  exact packed_row rowTable horizon stride bits 13 300 w13_300 (by decide +kernel) code
theorem walk_literal : walkRow soko3_1.board (soko3_1.initial.holes.drop 12) (phases.heroes 12) 300 (decodeDebt bits w12_300) = true := by decide +kernel
theorem walk_actual : walkRow soko3_1.board (soko3_1.initial.holes.drop 12) (phases.heroes 12) 300 (fun hero => weight 12 hero 300) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko3_1.board (soko3_1.initial.holes.drop 12) (phases.heroes 12) 300 (decodeDebt bits w12_300)
    (fun landing => weight 12 300 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko3_1.board (soko3_1.initial.holes.drop 12) (phases.heroes 12) 300 (fun hero => weight 12 hero 300)
    (fun landing => weight 12 300 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko3_1.board (soko3_1.initial.holes.drop 12) 300
    (decodeDebt bits w12_300) (decodeDebt bits w13_300) = true := by decide +kernel
theorem advance_actual : advanceRow soko3_1.board (soko3_1.initial.holes.drop 12) 300
    (fun hero => weight 12 hero 300) (fun hero => weight 13 hero 300) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko31Hero133.Checks.P12B300
