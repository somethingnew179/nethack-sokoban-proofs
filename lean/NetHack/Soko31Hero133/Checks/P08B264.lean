import NetHack.Soko31Hero133.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Hero133.Checks.P08B264
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 8 hero 264) = decodeDebt bits w08_264 := by
  have code : IndexedCertificateTable.get 0 rowTable (8 * stride + 264) = w08_264 := by decide +kernel
  exact packed_row rowTable horizon stride bits 8 264 w08_264 (by decide +kernel) code
theorem after_exact : (fun hero => weight 9 hero 264) = decodeDebt bits w09_264 := by
  have code : IndexedCertificateTable.get 0 rowTable (9 * stride + 264) = w09_264 := by decide +kernel
  exact packed_row rowTable horizon stride bits 9 264 w09_264 (by decide +kernel) code
theorem walk_literal : walkRow soko3_1.board (soko3_1.initial.holes.drop 8) (phases.heroes 8) 264 (decodeDebt bits w08_264) = true := by decide +kernel
theorem walk_actual : walkRow soko3_1.board (soko3_1.initial.holes.drop 8) (phases.heroes 8) 264 (fun hero => weight 8 hero 264) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko3_1.board (soko3_1.initial.holes.drop 8) (phases.heroes 8) 264 (decodeDebt bits w08_264)
    (fun landing => weight 8 264 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko3_1.board (soko3_1.initial.holes.drop 8) (phases.heroes 8) 264 (fun hero => weight 8 hero 264)
    (fun landing => weight 8 264 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko3_1.board (soko3_1.initial.holes.drop 8) 264
    (decodeDebt bits w08_264) (decodeDebt bits w09_264) = true := by decide +kernel
theorem advance_actual : advanceRow soko3_1.board (soko3_1.initial.holes.drop 8) 264
    (fun hero => weight 8 hero 264) (fun hero => weight 9 hero 264) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko31Hero133.Checks.P08B264
