import NetHack.Soko31Hero133.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Hero133.Checks.P03B147
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 3 hero 147) = decodeDebt bits w03_147 := by
  have code : IndexedCertificateTable.get 0 rowTable (3 * stride + 147) = w03_147 := by decide +kernel
  exact packed_row rowTable horizon stride bits 3 147 w03_147 (by decide +kernel) code
theorem after_exact : (fun hero => weight 4 hero 147) = decodeDebt bits w04_147 := by
  have code : IndexedCertificateTable.get 0 rowTable (4 * stride + 147) = w04_147 := by decide +kernel
  exact packed_row rowTable horizon stride bits 4 147 w04_147 (by decide +kernel) code
theorem walk_literal : walkRow soko3_1.board (soko3_1.initial.holes.drop 3) (phases.heroes 3) 147 (decodeDebt bits w03_147) = true := by decide +kernel
theorem walk_actual : walkRow soko3_1.board (soko3_1.initial.holes.drop 3) (phases.heroes 3) 147 (fun hero => weight 3 hero 147) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko3_1.board (soko3_1.initial.holes.drop 3) (phases.heroes 3) 147 (decodeDebt bits w03_147)
    (fun landing => weight 3 147 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko3_1.board (soko3_1.initial.holes.drop 3) (phases.heroes 3) 147 (fun hero => weight 3 hero 147)
    (fun landing => weight 3 147 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko3_1.board (soko3_1.initial.holes.drop 3) 147
    (decodeDebt bits w03_147) (decodeDebt bits w04_147) = true := by decide +kernel
theorem advance_actual : advanceRow soko3_1.board (soko3_1.initial.holes.drop 3) 147
    (fun hero => weight 3 hero 147) (fun hero => weight 4 hero 147) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko31Hero133.Checks.P03B147
