import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P14B212
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 14 hero 212) = decodeDebt bits w14_212 := by
  have code : IndexedCertificateTable.get 0 rowTable (14 * stride + 212) = w14_212 := by decide +kernel
  exact packed_row rowTable horizon stride bits 14 212 w14_212 (by decide +kernel) code
theorem after_exact : (fun hero => weight 15 hero 212) = decodeDebt bits w15_212 := by
  have code : IndexedCertificateTable.get 0 rowTable (15 * stride + 212) = w15_212 := by decide +kernel
  exact packed_row rowTable horizon stride bits 15 212 w15_212 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 14) (phases.heroes 14) 212 (decodeDebt bits w14_212) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 14) (phases.heroes 14) 212 (fun hero => weight 14 hero 212) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 14) (phases.heroes 14) 212 (decodeDebt bits w14_212)
    (fun landing => weight 14 212 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 14) (phases.heroes 14) 212 (fun hero => weight 14 hero 212)
    (fun landing => weight 14 212 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 14) 212
    (decodeDebt bits w14_212) (decodeDebt bits w15_212) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 14) 212
    (fun hero => weight 14 hero 212) (fun hero => weight 15 hero 212) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P14B212
