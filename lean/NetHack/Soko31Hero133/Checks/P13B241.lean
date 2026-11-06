import NetHack.Soko31Hero133.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Hero133.Checks.P13B241
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 13 hero 241) = decodeDebt bits w13_241 := by
  have code : IndexedCertificateTable.get 0 rowTable (13 * stride + 241) = w13_241 := by decide +kernel
  exact packed_row rowTable horizon stride bits 13 241 w13_241 (by decide +kernel) code
theorem after_exact : (fun hero => weight 14 hero 241) = decodeDebt bits w14_241 := by
  have code : IndexedCertificateTable.get 0 rowTable (14 * stride + 241) = w14_241 := by decide +kernel
  exact packed_row rowTable horizon stride bits 14 241 w14_241 (by decide +kernel) code
theorem walk_literal : walkRow soko3_1.board (soko3_1.initial.holes.drop 13) (phases.heroes 13) 241 (decodeDebt bits w13_241) = true := by decide +kernel
theorem walk_actual : walkRow soko3_1.board (soko3_1.initial.holes.drop 13) (phases.heroes 13) 241 (fun hero => weight 13 hero 241) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko3_1.board (soko3_1.initial.holes.drop 13) (phases.heroes 13) 241 (decodeDebt bits w13_241)
    (fun landing => weight 13 241 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko3_1.board (soko3_1.initial.holes.drop 13) (phases.heroes 13) 241 (fun hero => weight 13 hero 241)
    (fun landing => weight 13 241 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko3_1.board (soko3_1.initial.holes.drop 13) 241
    (decodeDebt bits w13_241) (decodeDebt bits w14_241) = true := by decide +kernel
theorem advance_actual : advanceRow soko3_1.board (soko3_1.initial.holes.drop 13) 241
    (fun hero => weight 13 hero 241) (fun hero => weight 14 hero 241) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko31Hero133.Checks.P13B241
