import NetHack.Soko31Hero133.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko31Hero133.Checks.P11B212
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 11 hero 212) = decodeDebt bits w11_212 := by
  have code : IndexedCertificateTable.get 0 rowTable (11 * stride + 212) = w11_212 := by decide +kernel
  exact packed_row rowTable horizon stride bits 11 212 w11_212 (by decide +kernel) code
theorem after_exact : (fun hero => weight 12 hero 212) = decodeDebt bits w12_212 := by
  have code : IndexedCertificateTable.get 0 rowTable (12 * stride + 212) = w12_212 := by decide +kernel
  exact packed_row rowTable horizon stride bits 12 212 w12_212 (by decide +kernel) code
theorem walk_literal : walkRow soko3_1.board (soko3_1.initial.holes.drop 11) (phases.heroes 11) 212 (decodeDebt bits w11_212) = true := by decide +kernel
theorem walk_actual : walkRow soko3_1.board (soko3_1.initial.holes.drop 11) (phases.heroes 11) 212 (fun hero => weight 11 hero 212) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko3_1.board (soko3_1.initial.holes.drop 11) (phases.heroes 11) 212 (decodeDebt bits w11_212)
    (fun landing => weight 11 212 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko3_1.board (soko3_1.initial.holes.drop 11) (phases.heroes 11) 212 (fun hero => weight 11 hero 212)
    (fun landing => weight 11 212 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko3_1.board (soko3_1.initial.holes.drop 11) 212
    (decodeDebt bits w11_212) (decodeDebt bits w12_212) = true := by decide +kernel
theorem advance_actual : advanceRow soko3_1.board (soko3_1.initial.holes.drop 11) 212
    (fun hero => weight 11 hero 212) (fun hero => weight 12 hero 212) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko31Hero133.Checks.P11B212
