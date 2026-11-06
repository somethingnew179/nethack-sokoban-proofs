import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P12B114
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 12 hero 114) = decodeDebt bits w12_114 := by
  have code : IndexedCertificateTable.get 0 rowTable (12 * stride + 114) = w12_114 := by decide +kernel
  exact packed_row rowTable horizon stride bits 12 114 w12_114 (by decide +kernel) code
theorem after_exact : (fun hero => weight 13 hero 114) = decodeDebt bits w13_114 := by
  have code : IndexedCertificateTable.get 0 rowTable (13 * stride + 114) = w13_114 := by decide +kernel
  exact packed_row rowTable horizon stride bits 13 114 w13_114 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 12) (phases.heroes 12) 114 (decodeDebt bits w12_114) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 12) (phases.heroes 12) 114 (fun hero => weight 12 hero 114) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 12) (phases.heroes 12) 114 (decodeDebt bits w12_114)
    (fun landing => weight 12 114 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 12) (phases.heroes 12) 114 (fun hero => weight 12 hero 114)
    (fun landing => weight 12 114 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 12) 114
    (decodeDebt bits w12_114) (decodeDebt bits w13_114) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 12) 114
    (fun hero => weight 12 hero 114) (fun hero => weight 13 hero 114) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P12B114
