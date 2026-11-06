import NetHack.Soko31Hero133.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Hero133.Checks.P05B299
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 5 hero 299) = decodeDebt bits w05_299 := by
  have code : IndexedCertificateTable.get 0 rowTable (5 * stride + 299) = w05_299 := by decide +kernel
  exact packed_row rowTable horizon stride bits 5 299 w05_299 (by decide +kernel) code
theorem after_exact : (fun hero => weight 6 hero 299) = decodeDebt bits w06_299 := by
  have code : IndexedCertificateTable.get 0 rowTable (6 * stride + 299) = w06_299 := by decide +kernel
  exact packed_row rowTable horizon stride bits 6 299 w06_299 (by decide +kernel) code
theorem walk_literal : walkRow soko3_1.board (soko3_1.initial.holes.drop 5) (phases.heroes 5) 299 (decodeDebt bits w05_299) = true := by decide +kernel
theorem walk_actual : walkRow soko3_1.board (soko3_1.initial.holes.drop 5) (phases.heroes 5) 299 (fun hero => weight 5 hero 299) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko3_1.board (soko3_1.initial.holes.drop 5) (phases.heroes 5) 299 (decodeDebt bits w05_299)
    (fun landing => weight 5 299 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko3_1.board (soko3_1.initial.holes.drop 5) (phases.heroes 5) 299 (fun hero => weight 5 hero 299)
    (fun landing => weight 5 299 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko3_1.board (soko3_1.initial.holes.drop 5) 299
    (decodeDebt bits w05_299) (decodeDebt bits w06_299) = true := by decide +kernel
theorem advance_actual : advanceRow soko3_1.board (soko3_1.initial.holes.drop 5) 299
    (fun hero => weight 5 hero 299) (fun hero => weight 6 hero 299) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko31Hero133.Checks.P05B299
