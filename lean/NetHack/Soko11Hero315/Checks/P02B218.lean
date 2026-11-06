import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P02B218
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 2 hero 218) = decodeDebt bits w02_218 := by
  have code : IndexedCertificateTable.get 0 rowTable (2 * stride + 218) = w02_218 := by decide +kernel
  exact packed_row rowTable horizon stride bits 2 218 w02_218 (by decide +kernel) code
theorem after_exact : (fun hero => weight 3 hero 218) = decodeDebt bits w03_218 := by
  have code : IndexedCertificateTable.get 0 rowTable (3 * stride + 218) = w03_218 := by decide +kernel
  exact packed_row rowTable horizon stride bits 3 218 w03_218 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 2) (phases.heroes 2) 218 (decodeDebt bits w02_218) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 2) (phases.heroes 2) 218 (fun hero => weight 2 hero 218) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 2) (phases.heroes 2) 218 (decodeDebt bits w02_218)
    (fun landing => weight 2 218 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 2) (phases.heroes 2) 218 (fun hero => weight 2 hero 218)
    (fun landing => weight 2 218 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 2) 218
    (decodeDebt bits w02_218) (decodeDebt bits w03_218) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 2) 218
    (fun hero => weight 2 hero 218) (fun hero => weight 3 hero 218) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P02B218
