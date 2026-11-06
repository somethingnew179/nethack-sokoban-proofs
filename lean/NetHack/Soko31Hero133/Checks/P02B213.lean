import NetHack.Soko31Hero133.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Hero133.Checks.P02B213
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 2 hero 213) = decodeDebt bits w02_213 := by
  have code : IndexedCertificateTable.get 0 rowTable (2 * stride + 213) = w02_213 := by decide +kernel
  exact packed_row rowTable horizon stride bits 2 213 w02_213 (by decide +kernel) code
theorem after_exact : (fun hero => weight 3 hero 213) = decodeDebt bits w03_213 := by
  have code : IndexedCertificateTable.get 0 rowTable (3 * stride + 213) = w03_213 := by decide +kernel
  exact packed_row rowTable horizon stride bits 3 213 w03_213 (by decide +kernel) code
theorem walk_literal : walkRow soko3_1.board (soko3_1.initial.holes.drop 2) (phases.heroes 2) 213 (decodeDebt bits w02_213) = true := by decide +kernel
theorem walk_actual : walkRow soko3_1.board (soko3_1.initial.holes.drop 2) (phases.heroes 2) 213 (fun hero => weight 2 hero 213) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko3_1.board (soko3_1.initial.holes.drop 2) (phases.heroes 2) 213 (decodeDebt bits w02_213)
    (fun landing => weight 2 213 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko3_1.board (soko3_1.initial.holes.drop 2) (phases.heroes 2) 213 (fun hero => weight 2 hero 213)
    (fun landing => weight 2 213 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko3_1.board (soko3_1.initial.holes.drop 2) 213
    (decodeDebt bits w02_213) (decodeDebt bits w03_213) = true := by decide +kernel
theorem advance_actual : advanceRow soko3_1.board (soko3_1.initial.holes.drop 2) 213
    (fun hero => weight 2 hero 213) (fun hero => weight 3 hero 213) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko31Hero133.Checks.P02B213
