import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P15B112
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 15 hero 112) = decodeDebt bits w15_112 := by
  have code : IndexedCertificateTable.get 0 rowTable (15 * stride + 112) = w15_112 := by decide +kernel
  exact packed_row rowTable horizon stride bits 15 112 w15_112 (by decide +kernel) code
theorem after_exact : (fun hero => weight 16 hero 112) = decodeDebt bits 0 := by
  funext hero
  change weight horizon hero 112 = decodeDebt bits 0 hero
  rw [terminal, decodeDebt_zero]
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 15) (phases.heroes 15) 112 (decodeDebt bits w15_112) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 15) (phases.heroes 15) 112 (fun hero => weight 15 hero 112) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 15) (phases.heroes 15) 112 (decodeDebt bits w15_112)
    (fun landing => weight 15 112 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 15) (phases.heroes 15) 112 (fun hero => weight 15 hero 112)
    (fun landing => weight 15 112 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 15) 112
    (decodeDebt bits w15_112) (decodeDebt bits 0) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 15) 112
    (fun hero => weight 15 hero 112) (fun hero => weight 16 hero 112) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P15B112
