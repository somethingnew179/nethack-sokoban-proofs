import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P02B294
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 2 hero 294) = decodeDebt bits w02_294 := by
  have code : IndexedCertificateTable.get 0 rowTable (2 * stride + 294) = w02_294 := by decide +kernel
  exact packed_row rowTable horizon stride bits 2 294 w02_294 (by decide +kernel) code
theorem after_exact : (fun hero => weight 3 hero 294) = decodeDebt bits w03_294 := by
  have code : IndexedCertificateTable.get 0 rowTable (3 * stride + 294) = w03_294 := by decide +kernel
  exact packed_row rowTable horizon stride bits 3 294 w03_294 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 2) (phases.heroes 2) 294 (decodeDebt bits w02_294) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 2) (phases.heroes 2) 294 (fun hero => weight 2 hero 294) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 2) (phases.heroes 2) 294 (decodeDebt bits w02_294)
    (fun landing => weight 2 294 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 2) (phases.heroes 2) 294 (fun hero => weight 2 hero 294)
    (fun landing => weight 2 294 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 2) 294
    (decodeDebt bits w02_294) (decodeDebt bits w03_294) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 2) 294
    (fun hero => weight 2 hero 294) (fun hero => weight 3 hero 294) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P02B294
