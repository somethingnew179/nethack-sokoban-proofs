import NetHack.Soko31Hero133.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Hero133.Checks.P14B37
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 14 hero 37) = decodeDebt bits 0 := by
  have code : IndexedCertificateTable.get 0 rowTable (14 * stride + 37) = 0 := by decide +kernel
  exact packed_row rowTable horizon stride bits 14 37 0 (by decide +kernel) code
theorem after_exact : (fun hero => weight 15 hero 37) = decodeDebt bits 0 := by
  funext hero
  change weight horizon hero 37 = decodeDebt bits 0 hero
  rw [terminal, decodeDebt_zero]
theorem walk_literal : walkRow soko3_1.board (soko3_1.initial.holes.drop 14) (phases.heroes 14) 37 (decodeDebt bits 0) = true := by decide +kernel
theorem walk_actual : walkRow soko3_1.board (soko3_1.initial.holes.drop 14) (phases.heroes 14) 37 (fun hero => weight 14 hero 37) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko3_1.board (soko3_1.initial.holes.drop 14) (phases.heroes 14) 37 (decodeDebt bits 0)
    (fun landing => weight 14 37 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko3_1.board (soko3_1.initial.holes.drop 14) (phases.heroes 14) 37 (fun hero => weight 14 hero 37)
    (fun landing => weight 14 37 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko3_1.board (soko3_1.initial.holes.drop 14) 37
    (decodeDebt bits 0) (decodeDebt bits 0) = true := by decide +kernel
theorem advance_actual : advanceRow soko3_1.board (soko3_1.initial.holes.drop 14) 37
    (fun hero => weight 14 hero 37) (fun hero => weight 15 hero 37) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko31Hero133.Checks.P14B37
