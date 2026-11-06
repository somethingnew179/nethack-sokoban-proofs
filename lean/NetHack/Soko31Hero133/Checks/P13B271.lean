import NetHack.Soko31Hero133.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Hero133.Checks.P13B271
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 13 hero 271) = decodeDebt bits w13_271 := by
  have code : IndexedCertificateTable.get 0 rowTable (13 * stride + 271) = w13_271 := by decide +kernel
  exact packed_row rowTable horizon stride bits 13 271 w13_271 (by decide +kernel) code
theorem after_exact : (fun hero => weight 14 hero 271) = decodeDebt bits w14_271 := by
  have code : IndexedCertificateTable.get 0 rowTable (14 * stride + 271) = w14_271 := by decide +kernel
  exact packed_row rowTable horizon stride bits 14 271 w14_271 (by decide +kernel) code
theorem walk_literal : walkRow soko3_1.board (soko3_1.initial.holes.drop 13) (phases.heroes 13) 271 (decodeDebt bits w13_271) = true := by decide +kernel
theorem walk_actual : walkRow soko3_1.board (soko3_1.initial.holes.drop 13) (phases.heroes 13) 271 (fun hero => weight 13 hero 271) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko3_1.board (soko3_1.initial.holes.drop 13) (phases.heroes 13) 271 (decodeDebt bits w13_271)
    (fun landing => weight 13 271 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko3_1.board (soko3_1.initial.holes.drop 13) (phases.heroes 13) 271 (fun hero => weight 13 hero 271)
    (fun landing => weight 13 271 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko3_1.board (soko3_1.initial.holes.drop 13) 271
    (decodeDebt bits w13_271) (decodeDebt bits w14_271) = true := by decide +kernel
theorem advance_actual : advanceRow soko3_1.board (soko3_1.initial.holes.drop 13) 271
    (fun hero => weight 13 hero 271) (fun hero => weight 14 hero 271) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko31Hero133.Checks.P13B271
