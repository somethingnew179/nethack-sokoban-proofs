import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P10B392
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 10 hero 392) = decodeDebt bits w10_392 := by
  have code : IndexedCertificateTable.get 0 rowTable (10 * stride + 392) = w10_392 := by decide +kernel
  exact packed_row rowTable horizon stride bits 10 392 w10_392 (by decide +kernel) code
theorem after_exact : (fun hero => weight 11 hero 392) = decodeDebt bits w11_392 := by
  have code : IndexedCertificateTable.get 0 rowTable (11 * stride + 392) = w11_392 := by decide +kernel
  exact packed_row rowTable horizon stride bits 11 392 w11_392 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 10) (phases.heroes 10) 392 (decodeDebt bits w10_392) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 10) (phases.heroes 10) 392 (fun hero => weight 10 hero 392) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 10) (phases.heroes 10) 392 (decodeDebt bits w10_392)
    (fun landing => weight 10 392 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 10) (phases.heroes 10) 392 (fun hero => weight 10 hero 392)
    (fun landing => weight 10 392 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 10) 392
    (decodeDebt bits w10_392) (decodeDebt bits w11_392) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 10) 392
    (fun hero => weight 10 hero 392) (fun hero => weight 11 hero 392) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P10B392
