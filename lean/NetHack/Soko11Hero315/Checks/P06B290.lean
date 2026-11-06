import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P06B290
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 6 hero 290) = decodeDebt bits w06_290 := by
  have code : IndexedCertificateTable.get 0 rowTable (6 * stride + 290) = w06_290 := by decide +kernel
  exact packed_row rowTable horizon stride bits 6 290 w06_290 (by decide +kernel) code
theorem after_exact : (fun hero => weight 7 hero 290) = decodeDebt bits w07_290 := by
  have code : IndexedCertificateTable.get 0 rowTable (7 * stride + 290) = w07_290 := by decide +kernel
  exact packed_row rowTable horizon stride bits 7 290 w07_290 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 6) (phases.heroes 6) 290 (decodeDebt bits w06_290) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 6) (phases.heroes 6) 290 (fun hero => weight 6 hero 290) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 6) (phases.heroes 6) 290 (decodeDebt bits w06_290)
    (fun landing => weight 6 290 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 6) (phases.heroes 6) 290 (fun hero => weight 6 hero 290)
    (fun landing => weight 6 290 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 6) 290
    (decodeDebt bits w06_290) (decodeDebt bits w07_290) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 6) 290
    (fun hero => weight 6 hero 290) (fun hero => weight 7 hero 290) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P06B290
