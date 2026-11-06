import NetHack.Soko31Hero133.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Hero133.Checks.P04B120
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 4 hero 120) = decodeDebt bits 0 := by
  have code : IndexedCertificateTable.get 0 rowTable (4 * stride + 120) = 0 := by decide +kernel
  exact packed_row rowTable horizon stride bits 4 120 0 (by decide +kernel) code
theorem after_exact : (fun hero => weight 5 hero 120) = decodeDebt bits 0 := by
  have code : IndexedCertificateTable.get 0 rowTable (5 * stride + 120) = 0 := by decide +kernel
  exact packed_row rowTable horizon stride bits 5 120 0 (by decide +kernel) code
theorem walk_literal : walkRow soko3_1.board (soko3_1.initial.holes.drop 4) (phases.heroes 4) 120 (decodeDebt bits 0) = true := by decide +kernel
theorem walk_actual : walkRow soko3_1.board (soko3_1.initial.holes.drop 4) (phases.heroes 4) 120 (fun hero => weight 4 hero 120) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko3_1.board (soko3_1.initial.holes.drop 4) (phases.heroes 4) 120 (decodeDebt bits 0)
    (fun landing => weight 4 120 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko3_1.board (soko3_1.initial.holes.drop 4) (phases.heroes 4) 120 (fun hero => weight 4 hero 120)
    (fun landing => weight 4 120 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko3_1.board (soko3_1.initial.holes.drop 4) 120
    (decodeDebt bits 0) (decodeDebt bits 0) = true := by decide +kernel
theorem advance_actual : advanceRow soko3_1.board (soko3_1.initial.holes.drop 4) 120
    (fun hero => weight 4 hero 120) (fun hero => weight 5 hero 120) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko31Hero133.Checks.P04B120
