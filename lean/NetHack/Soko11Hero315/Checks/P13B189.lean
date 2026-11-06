import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P13B189
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 13 hero 189) = decodeDebt bits w13_189 := by
  have code : IndexedCertificateTable.get 0 rowTable (13 * stride + 189) = w13_189 := by decide +kernel
  exact packed_row rowTable horizon stride bits 13 189 w13_189 (by decide +kernel) code
theorem after_exact : (fun hero => weight 14 hero 189) = decodeDebt bits w14_189 := by
  have code : IndexedCertificateTable.get 0 rowTable (14 * stride + 189) = w14_189 := by decide +kernel
  exact packed_row rowTable horizon stride bits 14 189 w14_189 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 13) (phases.heroes 13) 189 (decodeDebt bits w13_189) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 13) (phases.heroes 13) 189 (fun hero => weight 13 hero 189) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 13) (phases.heroes 13) 189 (decodeDebt bits w13_189)
    (fun landing => weight 13 189 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 13) (phases.heroes 13) 189 (fun hero => weight 13 hero 189)
    (fun landing => weight 13 189 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 13) 189
    (decodeDebt bits w13_189) (decodeDebt bits w14_189) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 13) 189
    (fun hero => weight 13 hero 189) (fun hero => weight 14 hero 189) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P13B189
