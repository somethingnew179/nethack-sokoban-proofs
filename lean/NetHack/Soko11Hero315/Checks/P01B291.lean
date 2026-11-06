import NetHack.Soko11Hero315.Reader
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko11Hero315.Checks.P01B291
open NetHack.Sokoban NetHack.Sokoban.HeroPhasePotential
theorem before_exact : (fun hero => weight 1 hero 291) = decodeDebt bits w01_291 := by
  have code : IndexedCertificateTable.get 0 rowTable (1 * stride + 291) = w01_291 := by decide +kernel
  exact packed_row rowTable horizon stride bits 1 291 w01_291 (by decide +kernel) code
theorem after_exact : (fun hero => weight 2 hero 291) = decodeDebt bits w02_291 := by
  have code : IndexedCertificateTable.get 0 rowTable (2 * stride + 291) = w02_291 := by decide +kernel
  exact packed_row rowTable horizon stride bits 2 291 w02_291 (by decide +kernel) code
theorem walk_literal : walkRow soko1_1.board (soko1_1.initial.holes.drop 1) (phases.heroes 1) 291 (decodeDebt bits w01_291) = true := by decide +kernel
theorem walk_actual : walkRow soko1_1.board (soko1_1.initial.holes.drop 1) (phases.heroes 1) 291 (fun hero => weight 1 hero 291) = true := by
  rw [before_exact]
  exact walk_literal
theorem push_literal : pushRow soko1_1.board (soko1_1.initial.holes.drop 1) (phases.heroes 1) 291 (decodeDebt bits w01_291)
    (fun landing => weight 1 291 landing) holeWeight = true := by decide +kernel
theorem push_actual : pushRow soko1_1.board (soko1_1.initial.holes.drop 1) (phases.heroes 1) 291 (fun hero => weight 1 hero 291)
    (fun landing => weight 1 291 landing) holeWeight = true := by
  rw [before_exact]
  exact push_literal
theorem advance_literal : advanceRow soko1_1.board (soko1_1.initial.holes.drop 1) 291
    (decodeDebt bits w01_291) (decodeDebt bits w02_291) = true := by decide +kernel
theorem advance_actual : advanceRow soko1_1.board (soko1_1.initial.holes.drop 1) 291
    (fun hero => weight 1 hero 291) (fun hero => weight 2 hero 291) = true := by
  rw [before_exact, after_exact]
  exact advance_literal
end NetHack.Soko11Hero315.Checks.P01B291
