import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P09B214
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 9 hero 214) = decodeDebt bits w09_214 := by
  have code : IndexedCertificateTable.get 0 rowTable (9 * stride + 214) = w09_214 := by decide +kernel
  exact packed_row rowTable horizon stride bits 9 214 w09_214 (by decide +kernel) code
theorem after_exact : (fun hero => weight 10 hero 214) = decodeDebt bits w10_214 := by
  have code : IndexedCertificateTable.get 0 rowTable (10 * stride + 214) = w10_214 := by decide +kernel
  exact packed_row rowTable horizon stride bits 10 214 w10_214 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 9) (phases.heroes 9) 214 (decodeDebt bits w09_214) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 9) (phases.heroes 9) 214 (fun hero => weight 9 hero 214) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 9) (phases.heroes 9) 214 (decodeDebt bits w09_214)
    (fun landing => weight 9 214 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 9) (phases.heroes 9) 214 (fun hero => weight 9 hero 214)
    (fun landing => weight 9 214 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 9) 214
    (decodeDebt bits w09_214) (decodeDebt bits w10_214) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 9) 214
    (fun hero => weight 9 hero 214) (fun hero => weight 10 hero 214) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P09B214
