import NetHack.Soko31Hero133.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Hero133.Checks.P09B212
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 9 hero 212) = decodeDebt bits w09_212 := by
  have code : IndexedCertificateTable.get 0 rowTable (9 * stride + 212) = w09_212 := by decide +kernel
  exact packed_row rowTable horizon stride bits 9 212 w09_212 (by decide +kernel) code
theorem after_exact : (fun hero => weight 10 hero 212) = decodeDebt bits w10_212 := by
  have code : IndexedCertificateTable.get 0 rowTable (10 * stride + 212) = w10_212 := by decide +kernel
  exact packed_row rowTable horizon stride bits 10 212 w10_212 (by decide +kernel) code
theorem walk_literal : walkRow soko3_1.board (soko3_1.initial.holes.drop 9) (phases.heroes 9) 212 (decodeDebt bits w09_212) = true := by decide +kernel
theorem walk_actual : walkRow soko3_1.board (soko3_1.initial.holes.drop 9) (phases.heroes 9) 212 (fun hero => weight 9 hero 212) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko3_1.board (soko3_1.initial.holes.drop 9) (phases.heroes 9) 212 (decodeDebt bits w09_212)
    (fun landing => weight 9 212 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko3_1.board (soko3_1.initial.holes.drop 9) (phases.heroes 9) 212 (fun hero => weight 9 hero 212)
    (fun landing => weight 9 212 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko3_1.board (soko3_1.initial.holes.drop 9) 212
    (decodeDebt bits w09_212) (decodeDebt bits w10_212) = true := by decide +kernel
theorem advance_actual : advanceRow soko3_1.board (soko3_1.initial.holes.drop 9) 212
    (fun hero => weight 9 hero 212) (fun hero => weight 10 hero 212) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko31Hero133.Checks.P09B212
