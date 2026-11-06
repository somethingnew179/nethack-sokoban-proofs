import NetHack.Soko31Hero133.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Hero133.Checks.P07B90
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 7 hero 90) = decodeDebt bits w07_90 := by
  have code : IndexedCertificateTable.get 0 rowTable (7 * stride + 90) = w07_90 := by decide +kernel
  exact packed_row rowTable horizon stride bits 7 90 w07_90 (by decide +kernel) code
theorem after_exact : (fun hero => weight 8 hero 90) = decodeDebt bits w08_90 := by
  have code : IndexedCertificateTable.get 0 rowTable (8 * stride + 90) = w08_90 := by decide +kernel
  exact packed_row rowTable horizon stride bits 8 90 w08_90 (by decide +kernel) code
theorem walk_literal : walkRow soko3_1.board (soko3_1.initial.holes.drop 7) (phases.heroes 7) 90 (decodeDebt bits w07_90) = true := by decide +kernel
theorem walk_actual : walkRow soko3_1.board (soko3_1.initial.holes.drop 7) (phases.heroes 7) 90 (fun hero => weight 7 hero 90) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko3_1.board (soko3_1.initial.holes.drop 7) (phases.heroes 7) 90 (decodeDebt bits w07_90)
    (fun landing => weight 7 90 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko3_1.board (soko3_1.initial.holes.drop 7) (phases.heroes 7) 90 (fun hero => weight 7 hero 90)
    (fun landing => weight 7 90 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko3_1.board (soko3_1.initial.holes.drop 7) 90
    (decodeDebt bits w07_90) (decodeDebt bits w08_90) = true := by decide +kernel
theorem advance_actual : advanceRow soko3_1.board (soko3_1.initial.holes.drop 7) 90
    (fun hero => weight 7 hero 90) (fun hero => weight 8 hero 90) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko31Hero133.Checks.P07B90
