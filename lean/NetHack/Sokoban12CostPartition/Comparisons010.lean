/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons009
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare1400 (p : Pattern) (guard : d0 p = 1) : d57 p ≤ (0 : Int) + d57 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1401 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d57 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1402 (p : Pattern) (guard : d794 p = 1) : d114 p ≤ (0 : Int) + d57 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d794, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1401 p hg
    simpa only [d794, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1403 (p : Pattern) (guard : d987 p = 1) : d115 p ≤ (0 : Int) + d57 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d987, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1400 p hg
    simpa only [d987, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d987, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1402 p hg
    simpa only [d987, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1404 (p : Pattern) (guard : d0 p = 1) : d63 p ≤ (0 : Int) + d63 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1405 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (0 : Int) + d63 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1406 (p : Pattern) (guard : d794 p = 1) : d116 p ≤ (0 : Int) + d63 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare320 p hg
    simpa only [d794, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1405 p hg
    simpa only [d794, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1407 (p : Pattern) (guard : d987 p = 1) : d117 p ≤ (0 : Int) + d63 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d987, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1404 p hg
    simpa only [d987, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d987, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1406 p hg
    simpa only [d987, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1408 (p : Pattern) (guard : d987 p = 1) : d118 p ≤ (0 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d118, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1403 p hg
    simpa only [d118, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d118, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1407 p hg
    simpa only [d118, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1409 (p : Pattern) (guard : d0 p = 1) : d122 p ≤ (0 : Int) + d121 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1410 (p : Pattern) (guard : d1 p = 1) : d121 p ≤ (0 : Int) + d121 p := by
  omega
theorem compare1411 (p : Pattern) (guard : d794 p = 1) : d123 p ≤ (0 : Int) + d121 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1410 p hg
    simpa only [d794, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare726 p hg
    simpa only [d794, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1412 (p : Pattern) (guard : d987 p = 1) : d124 p ≤ (0 : Int) + d121 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d987, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1409 p hg
    simpa only [d987, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d987, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1411 p hg
    simpa only [d987, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1413 (p : Pattern) (guard : d0 p = 1) : d129 p ≤ (0 : Int) + d128 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1414 (p : Pattern) (guard : d1 p = 1) : d128 p ≤ (0 : Int) + d128 p := by
  omega
theorem compare1415 (p : Pattern) (guard : d794 p = 1) : d130 p ≤ (0 : Int) + d128 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1414 p hg
    simpa only [d794, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare730 p hg
    simpa only [d794, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1416 (p : Pattern) (guard : d987 p = 1) : d131 p ≤ (0 : Int) + d128 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d987, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1413 p hg
    simpa only [d987, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d987, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1415 p hg
    simpa only [d987, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1417 (p : Pattern) (guard : d987 p = 1) : d132 p ≤ (0 : Int) + d988 p := by
  cases selected : p 141 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d132, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1412 p hg
    simpa only [d132, d988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d132, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1416 p hg
    simpa only [d132, d988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1418 (p : Pattern) (guard : d987 p = 1) : d133 p ≤ (0 : Int) + d989 p := by
  cases selected : p 134 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d133, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1408 p hg
    simpa only [d133, d989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d133, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1417 p hg
    simpa only [d133, d989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1419 (p : Pattern) (guard : d987 p = 1) : d134 p ≤ (0 : Int) + d990 p := by
  cases selected : p 133 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d134, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1399 p hg
    simpa only [d134, d990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d134, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1418 p hg
    simpa only [d134, d990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1420 (p : Pattern) (guard : d987 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare1421 (p : Pattern) (guard : d987 p = 1) : d135 p ≤ (0 : Int) + d991 p := by
  cases selected : p 133 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d135, d991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1418 p hg
    simpa only [d135, d991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d135, d991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1420 p hg
    simpa only [d135, d991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1422 (p : Pattern) (guard : d987 p = 1) : d136 p ≤ (0 : Int) + d992 p := by
  cases selected : p 132 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d136, d992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1419 p hg
    simpa only [d136, d992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d136, d992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1421 p hg
    simpa only [d136, d992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1423 (p : Pattern) (guard : d987 p = 1) : d67 p ≤ (0 : Int) + d67 p := by
  omega
theorem compare1424 (p : Pattern) (guard : d0 p = 1) : d140 p ≤ (0 : Int) + d139 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1425 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d139 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1426 (p : Pattern) (guard : d794 p = 1) : d141 p ≤ (0 : Int) + d139 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare290 p hg
    simpa only [d794, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1425 p hg
    simpa only [d794, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1427 (p : Pattern) (guard : d987 p = 1) : d142 p ≤ (0 : Int) + d139 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d987, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1424 p hg
    simpa only [d987, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d987, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1426 p hg
    simpa only [d987, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1428 (p : Pattern) (guard : d0 p = 1) : d147 p ≤ (0 : Int) + d146 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1429 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (0 : Int) + d146 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1430 (p : Pattern) (guard : d794 p = 1) : d148 p ≤ (0 : Int) + d146 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d794, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare307 p hg
    simpa only [d794, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d794, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1429 p hg
    simpa only [d794, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1431 (p : Pattern) (guard : d987 p = 1) : d149 p ≤ (0 : Int) + d146 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d987, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1428 p hg
    simpa only [d987, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d987, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1430 p hg
    simpa only [d987, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1432 (p : Pattern) (guard : d987 p = 1) : d150 p ≤ (0 : Int) + d993 p := by
  cases selected : p 141 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d150, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1427 p hg
    simpa only [d150, d993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d150, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1431 p hg
    simpa only [d150, d993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1433 (p : Pattern) (guard : d987 p = 1) : d151 p ≤ (0 : Int) + d994 p := by
  cases selected : p 134 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d151, d994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1432 p hg
    simpa only [d151, d994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d151, d994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1420 p hg
    simpa only [d151, d994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1434 (p : Pattern) (guard : d987 p = 1) : d152 p ≤ (0 : Int) + d995 p := by
  cases selected : p 133 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d152, d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1423 p hg
    simpa only [d152, d995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d152, d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1433 p hg
    simpa only [d152, d995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1435 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d139 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1436 (p : Pattern) (guard : d987 p = 1) : d154 p ≤ (0 : Int) + d139 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d987, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1435 p hg
    simpa only [d987, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d987, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1426 p hg
    simpa only [d987, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1437 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (0 : Int) + d146 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1438 (p : Pattern) (guard : d987 p = 1) : d156 p ≤ (0 : Int) + d146 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d987, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1437 p hg
    simpa only [d987, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d987, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1430 p hg
    simpa only [d987, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1439 (p : Pattern) (guard : d987 p = 1) : d157 p ≤ (0 : Int) + d993 p := by
  cases selected : p 141 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d157, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1436 p hg
    simpa only [d157, d993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d157, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1438 p hg
    simpa only [d157, d993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1440 (p : Pattern) (guard : d987 p = 1) : d158 p ≤ (0 : Int) + d994 p := by
  cases selected : p 134 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d158, d994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1439 p hg
    simpa only [d158, d994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d158, d994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1420 p hg
    simpa only [d158, d994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1441 (p : Pattern) (guard : d987 p = 1) : d159 p ≤ (0 : Int) + d996 p := by
  cases selected : p 133 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d159, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1440 p hg
    simpa only [d159, d996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d159, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1420 p hg
    simpa only [d159, d996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1442 (p : Pattern) (guard : d987 p = 1) : d160 p ≤ (0 : Int) + d997 p := by
  cases selected : p 132 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d160, d997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d160, d997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d160, d997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1441 p hg
    simpa only [d160, d997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1443 (p : Pattern) (guard : d987 p = 1) : d161 p ≤ (0 : Int) + d998 p := by
  cases selected : p 108 with
  | false =>
    have hg : d987 p = 1 := by simpa only [d161, d998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1422 p hg
    simpa only [d161, d998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d161, d998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1442 p hg
    simpa only [d161, d998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1444 (p : Pattern) (guard : d742 p = 1) : d64 p ≤ (0 : Int) + d64 p := by
  omega
theorem compare1445 (p : Pattern) (guard : d0 p = 1) : d107 p ≤ (0 : Int) + d122 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1446 (p : Pattern) (guard : d742 p = 1) : d108 p ≤ (0 : Int) + d179 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d108, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare324 p hg
    simpa only [d742, d108, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d108, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1445 p hg
    simpa only [d742, d108, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1447 (p : Pattern) (guard : d0 p = 1) : d110 p ≤ (0 : Int) + d129 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1448 (p : Pattern) (guard : d742 p = 1) : d111 p ≤ (0 : Int) + d237 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d111, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare327 p hg
    simpa only [d742, d111, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d111, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1447 p hg
    simpa only [d742, d111, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1449 (p : Pattern) (guard : d742 p = 1) : d112 p ≤ (0 : Int) + d238 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d112, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1446 p hg
    simpa only [d112, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d112, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1448 p hg
    simpa only [d112, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1450 (p : Pattern) (guard : d742 p = 1) : d113 p ≤ (0 : Int) + d239 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d113, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1444 p hg
    simpa only [d113, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d113, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1449 p hg
    simpa only [d113, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1451 (p : Pattern) (guard : d742 p = 1) : d134 p ≤ (0 : Int) + d243 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d134, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1450 p hg
    simpa only [d134, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d134, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare344 p hg
    simpa only [d134, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1452 (p : Pattern) (guard : d742 p = 1) : d136 p ≤ (0 : Int) + d245 p := by
  cases selected : p 132 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d136, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1451 p hg
    simpa only [d136, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d136, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare347 p hg
    simpa only [d136, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1453 (p : Pattern) (guard : d0 p = 1) : d57 p ≤ (0 : Int) + d153 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1454 (p : Pattern) (guard : d742 p = 1) : d57 p ≤ (0 : Int) + d186 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d742, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1453 p hg
    simpa only [d742, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1455 (p : Pattern) (guard : d0 p = 1) : d63 p ≤ (0 : Int) + d155 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1456 (p : Pattern) (guard : d742 p = 1) : d63 p ≤ (0 : Int) + d246 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare320 p hg
    simpa only [d742, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1455 p hg
    simpa only [d742, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1457 (p : Pattern) (guard : d742 p = 1) : d64 p ≤ (0 : Int) + d247 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d64, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1454 p hg
    simpa only [d64, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d64, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1456 p hg
    simpa only [d64, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1458 (p : Pattern) (guard : d742 p = 1) : d67 p ≤ (0 : Int) + d248 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d67, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1457 p hg
    simpa only [d67, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d67, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare346 p hg
    simpa only [d67, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1459 (p : Pattern) (guard : d742 p = 1) : d152 p ≤ (0 : Int) + d252 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d152, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1458 p hg
    simpa only [d152, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d152, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare357 p hg
    simpa only [d152, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1460 (p : Pattern) (guard : d742 p = 1) : d160 p ≤ (0 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d160, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1459 p hg
    simpa only [d160, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d160, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare365 p hg
    simpa only [d160, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1461 (p : Pattern) (guard : d742 p = 1) : d161 p ≤ (0 : Int) + d258 p := by
  cases selected : p 108 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d161, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1452 p hg
    simpa only [d161, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d161, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1460 p hg
    simpa only [d161, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1462 (p : Pattern) (guard : d742 p = 1) : d68 p ≤ (0 : Int) + d57 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d742, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1401 p hg
    simpa only [d742, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1463 (p : Pattern) (guard : d742 p = 1) : d69 p ≤ (0 : Int) + d63 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare320 p hg
    simpa only [d742, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1405 p hg
    simpa only [d742, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1464 (p : Pattern) (guard : d742 p = 1) : d70 p ≤ (0 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d70, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1462 p hg
    simpa only [d70, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d70, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1463 p hg
    simpa only [d70, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1465 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d107 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1466 (p : Pattern) (guard : d742 p = 1) : d229 p ≤ (0 : Int) + d108 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d229, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare324 p hg
    simpa only [d742, d229, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d229, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1465 p hg
    simpa only [d742, d229, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1467 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (0 : Int) + d110 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1468 (p : Pattern) (guard : d742 p = 1) : d230 p ≤ (0 : Int) + d111 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d230, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare327 p hg
    simpa only [d742, d230, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d230, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1467 p hg
    simpa only [d742, d230, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1469 (p : Pattern) (guard : d742 p = 1) : d231 p ≤ (0 : Int) + d112 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d231, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1466 p hg
    simpa only [d231, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d231, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1468 p hg
    simpa only [d231, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1470 (p : Pattern) (guard : d742 p = 1) : d232 p ≤ (0 : Int) + d113 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d232, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1464 p hg
    simpa only [d232, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d232, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1469 p hg
    simpa only [d232, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1471 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d114 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1472 (p : Pattern) (guard : d742 p = 1) : d68 p ≤ (0 : Int) + d115 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d68, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d742, d68, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d68, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1471 p hg
    simpa only [d742, d68, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1473 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (0 : Int) + d116 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1474 (p : Pattern) (guard : d742 p = 1) : d69 p ≤ (0 : Int) + d117 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d69, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare320 p hg
    simpa only [d742, d69, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d69, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1473 p hg
    simpa only [d742, d69, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1475 (p : Pattern) (guard : d742 p = 1) : d70 p ≤ (0 : Int) + d118 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d70, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1472 p hg
    simpa only [d70, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d70, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1474 p hg
    simpa only [d70, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1476 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d123 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1477 (p : Pattern) (guard : d742 p = 1) : d181 p ≤ (0 : Int) + d124 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d181, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare337 p hg
    simpa only [d742, d181, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d181, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1476 p hg
    simpa only [d742, d181, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1478 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (0 : Int) + d130 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1479 (p : Pattern) (guard : d742 p = 1) : d240 p ≤ (0 : Int) + d131 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d240, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare340 p hg
    simpa only [d742, d240, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d240, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1478 p hg
    simpa only [d742, d240, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1480 (p : Pattern) (guard : d742 p = 1) : d241 p ≤ (0 : Int) + d132 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d241, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1477 p hg
    simpa only [d241, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d241, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1479 p hg
    simpa only [d241, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1481 (p : Pattern) (guard : d742 p = 1) : d242 p ≤ (0 : Int) + d133 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d242, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1475 p hg
    simpa only [d242, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d242, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1480 p hg
    simpa only [d242, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1482 (p : Pattern) (guard : d742 p = 1) : d315 p ≤ (0 : Int) + d134 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d315, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1470 p hg
    simpa only [d315, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d315, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1481 p hg
    simpa only [d315, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1483 (p : Pattern) (guard : d0 p = 1) : d244 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1484 (p : Pattern) (guard : d773 p = 1) : d316 p ≤ (0 : Int) + d199 p := by
  cases selected : p 132 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d773, d316, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1482 p hg
    simpa only [d773, d316, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d773, d316, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1483 p hg
    simpa only [d773, d316, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1485 (p : Pattern) (guard : d742 p = 1) : d71 p ≤ (0 : Int) + d67 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d71, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1464 p hg
    simpa only [d71, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d71, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare346 p hg
    simpa only [d71, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1486 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1487 (p : Pattern) (guard : d742 p = 1) : d188 p ≤ (0 : Int) + d142 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d188, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare350 p hg
    simpa only [d742, d188, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d188, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1486 p hg
    simpa only [d742, d188, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1488 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (0 : Int) + d148 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1489 (p : Pattern) (guard : d742 p = 1) : d249 p ≤ (0 : Int) + d149 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d249, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare353 p hg
    simpa only [d742, d249, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d249, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1488 p hg
    simpa only [d742, d249, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1490 (p : Pattern) (guard : d742 p = 1) : d250 p ≤ (0 : Int) + d150 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d250, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1487 p hg
    simpa only [d250, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d250, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1489 p hg
    simpa only [d250, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1491 (p : Pattern) (guard : d742 p = 1) : d251 p ≤ (0 : Int) + d151 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d251, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1490 p hg
    simpa only [d251, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d251, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare346 p hg
    simpa only [d251, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1492 (p : Pattern) (guard : d742 p = 1) : d317 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d317, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1485 p hg
    simpa only [d317, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d317, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1491 p hg
    simpa only [d317, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1493 (p : Pattern) (guard : d0 p = 1) : d256 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1494 (p : Pattern) (guard : d773 p = 1) : d318 p ≤ (0 : Int) + d200 p := by
  cases selected : p 132 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d773, d318, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1492 p hg
    simpa only [d773, d318, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d773, d318, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1493 p hg
    simpa only [d773, d318, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1495 (p : Pattern) (guard : d773 p = 1) : d319 p ≤ (0 : Int) + d201 p := by
  cases selected : p 108 with
  | false =>
    have hg : d773 p = 1 := by simpa only [d319, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1484 p hg
    simpa only [d319, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d773 p = 1 := by simpa only [d319, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1494 p hg
    simpa only [d319, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1496 (p : Pattern) (guard : d0 p = 1) : d315 p ≤ (12 : Int) + d134 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1497 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (12 : Int) + d57 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1498 (p : Pattern) (guard : d742 p = 1) : d68 p ≤ (12 : Int) + d57 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare631 p hg
    simpa only [d742, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1497 p hg
    simpa only [d742, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1499 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (12 : Int) + d63 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1500 (p : Pattern) (guard : d742 p = 1) : d69 p ≤ (12 : Int) + d63 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare640 p hg
    simpa only [d742, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d742, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1501 (p : Pattern) (guard : d742 p = 1) : d70 p ≤ (12 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d70, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d70, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d70, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d70, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1502 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (12 : Int) + d7 p := by
  omega
theorem compare1503 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (12 : Int) + d7 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1502 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare635 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1504 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (12 : Int) + d7 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1502 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1503 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1505 (p : Pattern) (guard : d1 p = 1) : d121 p ≤ (12 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d121, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1504 p hg
    simpa only [d121, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d121, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare636 p hg
    simpa only [d121, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1506 (p : Pattern) (guard : d1 p = 1) : d122 p ≤ (12 : Int) + d106 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare654 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1505 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1507 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (12 : Int) + d107 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1508 (p : Pattern) (guard : d742 p = 1) : d181 p ≤ (12 : Int) + d108 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d181, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1506 p hg
    simpa only [d742, d181, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d181, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d742, d181, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1509 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (12 : Int) + d11 p := by
  omega
theorem compare1510 (p : Pattern) (guard : d1 p = 1) : d125 p ≤ (12 : Int) + d11 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1509 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare646 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1511 (p : Pattern) (guard : d1 p = 1) : d126 p ≤ (12 : Int) + d11 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1509 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1510 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1512 (p : Pattern) (guard : d1 p = 1) : d127 p ≤ (12 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d127, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1504 p hg
    simpa only [d127, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d127, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1511 p hg
    simpa only [d127, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1513 (p : Pattern) (guard : d1 p = 1) : d128 p ≤ (12 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d128, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1512 p hg
    simpa only [d128, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d128, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare660 p hg
    simpa only [d128, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1514 (p : Pattern) (guard : d1 p = 1) : d129 p ≤ (12 : Int) + d109 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare659 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1513 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1515 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (12 : Int) + d110 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1516 (p : Pattern) (guard : d742 p = 1) : d240 p ≤ (12 : Int) + d111 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d240, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1514 p hg
    simpa only [d742, d240, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d240, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1515 p hg
    simpa only [d742, d240, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1517 (p : Pattern) (guard : d742 p = 1) : d241 p ≤ (12 : Int) + d112 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d241, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1508 p hg
    simpa only [d241, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d241, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1516 p hg
    simpa only [d241, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1518 (p : Pattern) (guard : d742 p = 1) : d242 p ≤ (12 : Int) + d113 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d242, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1501 p hg
    simpa only [d242, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d242, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1517 p hg
    simpa only [d242, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1519 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (12 : Int) + d114 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1520 (p : Pattern) (guard : d742 p = 1) : d55 p ≤ (12 : Int) + d115 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare638 p hg
    simpa only [d742, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1519 p hg
    simpa only [d742, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1521 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (12 : Int) + d116 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1522 (p : Pattern) (guard : d742 p = 1) : d65 p ≤ (12 : Int) + d117 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare651 p hg
    simpa only [d742, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1521 p hg
    simpa only [d742, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1523 (p : Pattern) (guard : d742 p = 1) : d66 p ≤ (12 : Int) + d118 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d66, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1520 p hg
    simpa only [d66, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d66, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1522 p hg
    simpa only [d66, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1524 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (12 : Int) + d119 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare635 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare636 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1525 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (12 : Int) + d120 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare635 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1524 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1526 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (12 : Int) + d121 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1525 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare636 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1527 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (12 : Int) + d122 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare655 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1526 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1528 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (12 : Int) + d123 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1529 (p : Pattern) (guard : d742 p = 1) : d55 p ≤ (12 : Int) + d124 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1527 p hg
    simpa only [d742, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1528 p hg
    simpa only [d742, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1530 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (12 : Int) + d125 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare646 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare648 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1531 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (12 : Int) + d126 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare646 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1530 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1532 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (12 : Int) + d127 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1525 p hg
    simpa only [d65, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1531 p hg
    simpa only [d65, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1533 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (12 : Int) + d128 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1532 p hg
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare660 p hg
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1534 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (12 : Int) + d129 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare661 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1533 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1535 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (12 : Int) + d130 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1536 (p : Pattern) (guard : d742 p = 1) : d65 p ≤ (12 : Int) + d131 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1534 p hg
    simpa only [d742, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1535 p hg
    simpa only [d742, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1537 (p : Pattern) (guard : d742 p = 1) : d66 p ≤ (12 : Int) + d132 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d66, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1529 p hg
    simpa only [d66, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d66, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1536 p hg
    simpa only [d66, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1538 (p : Pattern) (guard : d742 p = 1) : d66 p ≤ (12 : Int) + d133 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1523 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1537 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1539 (p : Pattern) (guard : d742 p = 1) : d244 p ≤ (12 : Int) + d134 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d244, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1518 p hg
    simpa only [d244, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d244, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1538 p hg
    simpa only [d244, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
