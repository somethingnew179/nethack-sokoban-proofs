import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P11B59
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 11 hero 59) = decodeDebt bits w11_59 := by
  have code : IndexedCertificateTable.get 0 rowTable (11 * stride + 59) = w11_59 := by decide +kernel
  exact packed_row rowTable horizon stride bits 11 59 w11_59 (by decide +kernel) code
theorem after_exact : (fun hero => weight 12 hero 59) = decodeDebt bits w12_59 := by
  have code : IndexedCertificateTable.get 0 rowTable (12 * stride + 59) = w12_59 := by decide +kernel
  exact packed_row rowTable horizon stride bits 12 59 w12_59 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 11) (phases.heroes 11) 59 (decodeDebt bits w11_59) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 11) (phases.heroes 11) 59 (fun hero => weight 11 hero 59) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 11) (phases.heroes 11) 59 (decodeDebt bits w11_59)
    (fun landing => weight 11 59 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 11) (phases.heroes 11) 59 (fun hero => weight 11 hero 59)
    (fun landing => weight 11 59 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 11) 59
    (decodeDebt bits w11_59) (decodeDebt bits w12_59) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 11) 59
    (fun hero => weight 11 hero 59) (fun hero => weight 12 hero 59) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P11B59
