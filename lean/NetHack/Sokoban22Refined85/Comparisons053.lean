/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons052
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare7420 (p : Pattern) (guard : d4670 p = 1) : d792 p ≤ (0 : Int) + d1402 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d792, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7418 p hg
    simpa only [d4670, d792, d1402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d792, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7419 p hg
    simpa only [d4670, d792, d1402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7421 (p : Pattern) (guard : d4670 p = 1) : d793 p ≤ (0 : Int) + d1403 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d793, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7416 p hg
    simpa only [d793, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d793, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7420 p hg
    simpa only [d793, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7422 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d1165 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7423 (p : Pattern) (guard : d4395 p = 1) : d56 p ≤ (0 : Int) + d1404 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d56, d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d56, d1404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d56, d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7422 p hg
    simpa only [d4395, d56, d1404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7424 (p : Pattern) (guard : d0 p = 1) : d387 p ≤ (0 : Int) + d1405 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7425 (p : Pattern) (guard : d4670 p = 1) : d794 p ≤ (0 : Int) + d1406 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d794, d1406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7423 p hg
    simpa only [d4670, d794, d1406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d794, d1406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7424 p hg
    simpa only [d4670, d794, d1406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7426 (p : Pattern) (guard : d0 p = 1) : d798 p ≤ (0 : Int) + d1171 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7427 (p : Pattern) (guard : d4395 p = 1) : d799 p ≤ (0 : Int) + d1407 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d799, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6412 p hg
    simpa only [d4395, d799, d1407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d799, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7426 p hg
    simpa only [d4395, d799, d1407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7428 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d177 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7429 (p : Pattern) (guard : d4670 p = 1) : d800 p ≤ (0 : Int) + d1408 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d800, d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7427 p hg
    simpa only [d4670, d800, d1408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d800, d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7428 p hg
    simpa only [d4670, d800, d1408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7430 (p : Pattern) (guard : d4670 p = 1) : d801 p ≤ (0 : Int) + d1409 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d801, d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7425 p hg
    simpa only [d801, d1409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d801, d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7429 p hg
    simpa only [d801, d1409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7431 (p : Pattern) (guard : d4670 p = 1) : d802 p ≤ (0 : Int) + d1410 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d802, d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7421 p hg
    simpa only [d802, d1410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d802, d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7430 p hg
    simpa only [d802, d1410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7432 (p : Pattern) (guard : d0 p = 1) : d394 p ≤ (0 : Int) + d1411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7433 (p : Pattern) (guard : d4670 p = 1) : d803 p ≤ (0 : Int) + d1412 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d803, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7414 p hg
    simpa only [d4670, d803, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d803, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7432 p hg
    simpa only [d4670, d803, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7434 (p : Pattern) (guard : d0 p = 1) : d79 p ≤ (0 : Int) + d63 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7435 (p : Pattern) (guard : d4395 p = 1) : d804 p ≤ (0 : Int) + d1413 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d804, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4395, d804, d1413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d804, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7434 p hg
    simpa only [d4395, d804, d1413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7436 (p : Pattern) (guard : d4670 p = 1) : d805 p ≤ (0 : Int) + d1414 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d805, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7435 p hg
    simpa only [d4670, d805, d1414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d805, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4670, d805, d1414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7437 (p : Pattern) (guard : d4670 p = 1) : d806 p ≤ (0 : Int) + d1415 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d806, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7433 p hg
    simpa only [d806, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d806, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7436 p hg
    simpa only [d806, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7438 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d1181 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7439 (p : Pattern) (guard : d4395 p = 1) : d56 p ≤ (0 : Int) + d1416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d56, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d56, d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d56, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7438 p hg
    simpa only [d4395, d56, d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7440 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1417 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7441 (p : Pattern) (guard : d4670 p = 1) : d807 p ≤ (0 : Int) + d1418 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d807, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7439 p hg
    simpa only [d4670, d807, d1418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d807, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7440 p hg
    simpa only [d4670, d807, d1418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7442 (p : Pattern) (guard : d4670 p = 1) : d812 p ≤ (0 : Int) + d1419 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d812, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7441 p hg
    simpa only [d812, d1419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d812, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6433 p hg
    simpa only [d812, d1419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7443 (p : Pattern) (guard : d4670 p = 1) : d813 p ≤ (0 : Int) + d1420 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d813, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7437 p hg
    simpa only [d813, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d813, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7442 p hg
    simpa only [d813, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7444 (p : Pattern) (guard : d4670 p = 1) : d814 p ≤ (0 : Int) + d1421 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d814, d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7431 p hg
    simpa only [d814, d1421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d814, d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7443 p hg
    simpa only [d814, d1421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7445 (p : Pattern) (guard : d0 p = 1) : d403 p ≤ (0 : Int) + d1411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7446 (p : Pattern) (guard : d4670 p = 1) : d815 p ≤ (0 : Int) + d1412 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d815, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7414 p hg
    simpa only [d4670, d815, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d815, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7445 p hg
    simpa only [d4670, d815, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7447 (p : Pattern) (guard : d4670 p = 1) : d816 p ≤ (0 : Int) + d1415 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d816, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7446 p hg
    simpa only [d816, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d816, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7436 p hg
    simpa only [d816, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7448 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (0 : Int) + d1417 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7449 (p : Pattern) (guard : d4670 p = 1) : d817 p ≤ (0 : Int) + d1418 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d817, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7439 p hg
    simpa only [d4670, d817, d1418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d817, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7448 p hg
    simpa only [d4670, d817, d1418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7450 (p : Pattern) (guard : d4670 p = 1) : d818 p ≤ (0 : Int) + d1419 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d818, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7449 p hg
    simpa only [d818, d1419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d818, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6433 p hg
    simpa only [d818, d1419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7451 (p : Pattern) (guard : d4670 p = 1) : d819 p ≤ (0 : Int) + d1420 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d819, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7447 p hg
    simpa only [d819, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d819, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7450 p hg
    simpa only [d819, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7452 (p : Pattern) (guard : d4395 p = 1) : d90 p ≤ (0 : Int) + d90 p := by
  omega
theorem compare7453 (p : Pattern) (guard : d4670 p = 1) : d820 p ≤ (0 : Int) + d92 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d820, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7452 p hg
    simpa only [d4670, d820, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d820, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6449 p hg
    simpa only [d4670, d820, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7454 (p : Pattern) (guard : d4670 p = 1) : d821 p ≤ (0 : Int) + d94 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d821, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7453 p hg
    simpa only [d821, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d821, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6451 p hg
    simpa only [d821, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7455 (p : Pattern) (guard : d4670 p = 1) : d822 p ≤ (0 : Int) + d96 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d822, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7454 p hg
    simpa only [d822, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d822, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6453 p hg
    simpa only [d822, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7456 (p : Pattern) (guard : d4670 p = 1) : d823 p ≤ (0 : Int) + d1422 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d823, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7451 p hg
    simpa only [d823, d1422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d823, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7455 p hg
    simpa only [d823, d1422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7457 (p : Pattern) (guard : d4670 p = 1) : d824 p ≤ (0 : Int) + d1423 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d824, d1423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7444 p hg
    simpa only [d824, d1423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d824, d1423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7456 p hg
    simpa only [d824, d1423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7458 (p : Pattern) (guard : d0 p = 1) : d390 p ≤ (0 : Int) + d1399 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7459 (p : Pattern) (guard : d4670 p = 1) : d825 p ≤ (0 : Int) + d1400 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d825, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7414 p hg
    simpa only [d4670, d825, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d825, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7458 p hg
    simpa only [d4670, d825, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7460 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d50 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7461 (p : Pattern) (guard : d4670 p = 1) : d826 p ≤ (0 : Int) + d1402 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d826, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7418 p hg
    simpa only [d4670, d826, d1402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d826, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7460 p hg
    simpa only [d4670, d826, d1402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7462 (p : Pattern) (guard : d4670 p = 1) : d827 p ≤ (0 : Int) + d1403 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d827, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7459 p hg
    simpa only [d827, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d827, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7461 p hg
    simpa only [d827, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7463 (p : Pattern) (guard : d0 p = 1) : d394 p ≤ (0 : Int) + d1405 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7464 (p : Pattern) (guard : d4670 p = 1) : d828 p ≤ (0 : Int) + d1424 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d828, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7439 p hg
    simpa only [d4670, d828, d1424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d828, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7463 p hg
    simpa only [d4670, d828, d1424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7465 (p : Pattern) (guard : d4670 p = 1) : d829 p ≤ (0 : Int) + d1425 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d829, d1425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7464 p hg
    simpa only [d829, d1425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d829, d1425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7429 p hg
    simpa only [d829, d1425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7466 (p : Pattern) (guard : d4670 p = 1) : d830 p ≤ (0 : Int) + d1426 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d830, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7462 p hg
    simpa only [d830, d1426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d830, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7465 p hg
    simpa only [d830, d1426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7467 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7468 (p : Pattern) (guard : d4670 p = 1) : d831 p ≤ (0 : Int) + d1412 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d831, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7414 p hg
    simpa only [d4670, d831, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d831, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7467 p hg
    simpa only [d4670, d831, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7469 (p : Pattern) (guard : d4670 p = 1) : d832 p ≤ (0 : Int) + d1415 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d832, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7468 p hg
    simpa only [d832, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d832, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7436 p hg
    simpa only [d832, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7470 (p : Pattern) (guard : d4670 p = 1) : d833 p ≤ (0 : Int) + d1420 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d833, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7469 p hg
    simpa only [d833, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d833, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7442 p hg
    simpa only [d833, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7471 (p : Pattern) (guard : d4670 p = 1) : d834 p ≤ (0 : Int) + d1427 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d834, d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7466 p hg
    simpa only [d834, d1427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d834, d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7470 p hg
    simpa only [d834, d1427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7472 (p : Pattern) (guard : d4670 p = 1) : d835 p ≤ (0 : Int) + d1428 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d835, d1428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7470 p hg
    simpa only [d835, d1428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d835, d1428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6484 p hg
    simpa only [d835, d1428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7473 (p : Pattern) (guard : d4670 p = 1) : d836 p ≤ (0 : Int) + d1429 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d836, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7471 p hg
    simpa only [d836, d1429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d836, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7472 p hg
    simpa only [d836, d1429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7474 (p : Pattern) (guard : d4670 p = 1) : d837 p ≤ (0 : Int) + d1430 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d837, d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7457 p hg
    simpa only [d837, d1430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d837, d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7473 p hg
    simpa only [d837, d1430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7475 (p : Pattern) (guard : d0 p = 1) : d372 p ≤ (0 : Int) + d1399 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7476 (p : Pattern) (guard : d4670 p = 1) : d838 p ≤ (0 : Int) + d1400 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d838, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7414 p hg
    simpa only [d4670, d838, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d838, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7475 p hg
    simpa only [d4670, d838, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7477 (p : Pattern) (guard : d4670 p = 1) : d839 p ≤ (0 : Int) + d1403 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d839, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7476 p hg
    simpa only [d839, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d839, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7461 p hg
    simpa only [d839, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7478 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d1167 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7479 (p : Pattern) (guard : d4395 p = 1) : d56 p ≤ (0 : Int) + d1431 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d56, d1431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d56, d1431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d56, d1431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7478 p hg
    simpa only [d4395, d56, d1431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7480 (p : Pattern) (guard : d0 p = 1) : d390 p ≤ (0 : Int) + d1405 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7481 (p : Pattern) (guard : d4670 p = 1) : d840 p ≤ (0 : Int) + d1432 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d840, d1432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7479 p hg
    simpa only [d4670, d840, d1432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d840, d1432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7480 p hg
    simpa only [d4670, d840, d1432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7482 (p : Pattern) (guard : d4670 p = 1) : d841 p ≤ (0 : Int) + d1433 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d841, d1433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7481 p hg
    simpa only [d841, d1433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d841, d1433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7429 p hg
    simpa only [d841, d1433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7483 (p : Pattern) (guard : d4670 p = 1) : d842 p ≤ (0 : Int) + d1434 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d842, d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7477 p hg
    simpa only [d842, d1434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d842, d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7482 p hg
    simpa only [d842, d1434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7484 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (0 : Int) + d1411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7485 (p : Pattern) (guard : d4670 p = 1) : d843 p ≤ (0 : Int) + d1412 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d843, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7414 p hg
    simpa only [d4670, d843, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d843, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7484 p hg
    simpa only [d4670, d843, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7486 (p : Pattern) (guard : d4670 p = 1) : d844 p ≤ (0 : Int) + d1415 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d844, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7485 p hg
    simpa only [d844, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d844, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7436 p hg
    simpa only [d844, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7487 (p : Pattern) (guard : d4670 p = 1) : d845 p ≤ (0 : Int) + d1420 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d845, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7486 p hg
    simpa only [d845, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d845, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7442 p hg
    simpa only [d845, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7488 (p : Pattern) (guard : d4670 p = 1) : d846 p ≤ (0 : Int) + d1435 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d846, d1435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7483 p hg
    simpa only [d846, d1435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d846, d1435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7487 p hg
    simpa only [d846, d1435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7489 (p : Pattern) (guard : d4670 p = 1) : d847 p ≤ (0 : Int) + d1422 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d847, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7443 p hg
    simpa only [d847, d1422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d847, d1422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7455 p hg
    simpa only [d847, d1422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7490 (p : Pattern) (guard : d4670 p = 1) : d848 p ≤ (0 : Int) + d1436 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d848, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7488 p hg
    simpa only [d848, d1436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d848, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7489 p hg
    simpa only [d848, d1436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7491 (p : Pattern) (guard : d0 p = 1) : d403 p ≤ (0 : Int) + d1399 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7492 (p : Pattern) (guard : d4670 p = 1) : d815 p ≤ (0 : Int) + d1400 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d815, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7414 p hg
    simpa only [d4670, d815, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d815, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7491 p hg
    simpa only [d4670, d815, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7493 (p : Pattern) (guard : d4670 p = 1) : d849 p ≤ (0 : Int) + d1403 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d849, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7492 p hg
    simpa only [d849, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d849, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7461 p hg
    simpa only [d849, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7494 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (0 : Int) + d1405 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7495 (p : Pattern) (guard : d4670 p = 1) : d817 p ≤ (0 : Int) + d1424 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d817, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7439 p hg
    simpa only [d4670, d817, d1424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d817, d1424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7494 p hg
    simpa only [d4670, d817, d1424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7496 (p : Pattern) (guard : d4670 p = 1) : d850 p ≤ (0 : Int) + d1425 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d850, d1425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7495 p hg
    simpa only [d850, d1425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d850, d1425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7429 p hg
    simpa only [d850, d1425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7497 (p : Pattern) (guard : d4670 p = 1) : d851 p ≤ (0 : Int) + d1426 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d851, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7493 p hg
    simpa only [d851, d1426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d851, d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7496 p hg
    simpa only [d851, d1426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7498 (p : Pattern) (guard : d4670 p = 1) : d852 p ≤ (0 : Int) + d1427 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d852, d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7497 p hg
    simpa only [d852, d1427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d852, d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7470 p hg
    simpa only [d852, d1427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7499 (p : Pattern) (guard : d4670 p = 1) : d853 p ≤ (0 : Int) + d1429 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d853, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7498 p hg
    simpa only [d853, d1429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d853, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7472 p hg
    simpa only [d853, d1429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7500 (p : Pattern) (guard : d4670 p = 1) : d854 p ≤ (0 : Int) + d1437 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d854, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7490 p hg
    simpa only [d854, d1437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d854, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7499 p hg
    simpa only [d854, d1437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7501 (p : Pattern) (guard : d4670 p = 1) : d855 p ≤ (0 : Int) + d1438 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d855, d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7474 p hg
    simpa only [d855, d1438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d855, d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7500 p hg
    simpa only [d855, d1438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7502 (p : Pattern) (guard : d4395 p = 1) : d111 p ≤ (0 : Int) + d111 p := by
  omega
theorem compare7503 (p : Pattern) (guard : d0 p = 1) : d372 p ≤ (0 : Int) + d1439 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7504 (p : Pattern) (guard : d4670 p = 1) : d856 p ≤ (0 : Int) + d1440 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d856, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7502 p hg
    simpa only [d4670, d856, d1440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d856, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7503 p hg
    simpa only [d4670, d856, d1440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7505 (p : Pattern) (guard : d0 p = 1) : d149 p ≤ (0 : Int) + d126 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7506 (p : Pattern) (guard : d4395 p = 1) : d857 p ≤ (0 : Int) + d1441 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d857, d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3757 p hg
    simpa only [d4395, d857, d1441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d857, d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7505 p hg
    simpa only [d4395, d857, d1441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7507 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d129 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7508 (p : Pattern) (guard : d4670 p = 1) : d858 p ≤ (0 : Int) + d1442 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d858, d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7506 p hg
    simpa only [d4670, d858, d1442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d858, d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7507 p hg
    simpa only [d4670, d858, d1442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7509 (p : Pattern) (guard : d4670 p = 1) : d859 p ≤ (0 : Int) + d1443 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d859, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7504 p hg
    simpa only [d859, d1443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d859, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7508 p hg
    simpa only [d859, d1443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7510 (p : Pattern) (guard : d0 p = 1) : d134 p ≤ (0 : Int) + d1284 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7511 (p : Pattern) (guard : d4395 p = 1) : d135 p ≤ (0 : Int) + d1444 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d135, d1444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d135, d1444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d135, d1444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7510 p hg
    simpa only [d4395, d135, d1444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7512 (p : Pattern) (guard : d4670 p = 1) : d860 p ≤ (0 : Int) + d1445 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d860, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7511 p hg
    simpa only [d4670, d860, d1445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d860, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6532 p hg
    simpa only [d4670, d860, d1445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7513 (p : Pattern) (guard : d0 p = 1) : d863 p ≤ (0 : Int) + d1290 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7514 (p : Pattern) (guard : d4395 p = 1) : d864 p ≤ (0 : Int) + d1446 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d864, d1446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6534 p hg
    simpa only [d4395, d864, d1446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d864, d1446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7513 p hg
    simpa only [d4395, d864, d1446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7515 (p : Pattern) (guard : d4670 p = 1) : d865 p ≤ (0 : Int) + d1447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d865, d1447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7514 p hg
    simpa only [d4670, d865, d1447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d865, d1447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6537 p hg
    simpa only [d4670, d865, d1447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7516 (p : Pattern) (guard : d4670 p = 1) : d866 p ≤ (0 : Int) + d1448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d866, d1448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7512 p hg
    simpa only [d866, d1448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d866, d1448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7515 p hg
    simpa only [d866, d1448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7517 (p : Pattern) (guard : d4670 p = 1) : d867 p ≤ (0 : Int) + d1449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d867, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7509 p hg
    simpa only [d867, d1449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d867, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7516 p hg
    simpa only [d867, d1449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7518 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (0 : Int) + d1450 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7519 (p : Pattern) (guard : d4670 p = 1) : d868 p ≤ (0 : Int) + d1451 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d868, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7502 p hg
    simpa only [d4670, d868, d1451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d868, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7518 p hg
    simpa only [d4670, d868, d1451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7520 (p : Pattern) (guard : d4670 p = 1) : d871 p ≤ (0 : Int) + d1452 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d871, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7519 p hg
    simpa only [d871, d1452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d871, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6546 p hg
    simpa only [d871, d1452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7521 (p : Pattern) (guard : d0 p = 1) : d134 p ≤ (0 : Int) + d1289 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7522 (p : Pattern) (guard : d4395 p = 1) : d135 p ≤ (0 : Int) + d1453 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d135, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d135, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d135, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7521 p hg
    simpa only [d4395, d135, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7523 (p : Pattern) (guard : d4670 p = 1) : d872 p ≤ (0 : Int) + d1454 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d872, d1454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7522 p hg
    simpa only [d4670, d872, d1454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d872, d1454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6550 p hg
    simpa only [d4670, d872, d1454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7524 (p : Pattern) (guard : d4670 p = 1) : d876 p ≤ (0 : Int) + d1455 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d876, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7523 p hg
    simpa only [d876, d1455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d876, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6555 p hg
    simpa only [d876, d1455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7525 (p : Pattern) (guard : d4670 p = 1) : d877 p ≤ (0 : Int) + d1456 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d877, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7520 p hg
    simpa only [d877, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d877, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7524 p hg
    simpa only [d877, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7526 (p : Pattern) (guard : d4670 p = 1) : d878 p ≤ (0 : Int) + d1457 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d878, d1457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7517 p hg
    simpa only [d878, d1457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d878, d1457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7525 p hg
    simpa only [d878, d1457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7527 (p : Pattern) (guard : d0 p = 1) : d394 p ≤ (0 : Int) + d1450 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7528 (p : Pattern) (guard : d4670 p = 1) : d879 p ≤ (0 : Int) + d1451 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d879, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7502 p hg
    simpa only [d4670, d879, d1451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d879, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7527 p hg
    simpa only [d4670, d879, d1451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7529 (p : Pattern) (guard : d4670 p = 1) : d880 p ≤ (0 : Int) + d1452 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d880, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7528 p hg
    simpa only [d880, d1452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d880, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6546 p hg
    simpa only [d880, d1452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7530 (p : Pattern) (guard : d4670 p = 1) : d881 p ≤ (0 : Int) + d1456 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d881, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7529 p hg
    simpa only [d881, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d881, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7524 p hg
    simpa only [d881, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7531 (p : Pattern) (guard : d4670 p = 1) : d882 p ≤ (0 : Int) + d1458 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d882, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7530 p hg
    simpa only [d882, d1458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d882, d1458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6568 p hg
    simpa only [d882, d1458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7532 (p : Pattern) (guard : d4670 p = 1) : d883 p ≤ (0 : Int) + d1459 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d883, d1459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7526 p hg
    simpa only [d883, d1459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d883, d1459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7531 p hg
    simpa only [d883, d1459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7533 (p : Pattern) (guard : d0 p = 1) : d403 p ≤ (0 : Int) + d1439 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7534 (p : Pattern) (guard : d4670 p = 1) : d884 p ≤ (0 : Int) + d1440 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d884, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7502 p hg
    simpa only [d4670, d884, d1440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d884, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7533 p hg
    simpa only [d4670, d884, d1440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7535 (p : Pattern) (guard : d4670 p = 1) : d885 p ≤ (0 : Int) + d1443 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d885, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7534 p hg
    simpa only [d885, d1443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d885, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7508 p hg
    simpa only [d885, d1443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7536 (p : Pattern) (guard : d4670 p = 1) : d886 p ≤ (0 : Int) + d1460 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d886, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7522 p hg
    simpa only [d4670, d886, d1460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d886, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6579 p hg
    simpa only [d4670, d886, d1460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7537 (p : Pattern) (guard : d4670 p = 1) : d887 p ≤ (0 : Int) + d1461 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d887, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7536 p hg
    simpa only [d887, d1461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d887, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7515 p hg
    simpa only [d887, d1461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7538 (p : Pattern) (guard : d4670 p = 1) : d888 p ≤ (0 : Int) + d1462 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d888, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7535 p hg
    simpa only [d888, d1462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d888, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7537 p hg
    simpa only [d888, d1462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7539 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1450 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7540 (p : Pattern) (guard : d4670 p = 1) : d889 p ≤ (0 : Int) + d1451 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d889, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7502 p hg
    simpa only [d4670, d889, d1451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d889, d1451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7539 p hg
    simpa only [d4670, d889, d1451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7541 (p : Pattern) (guard : d4670 p = 1) : d890 p ≤ (0 : Int) + d1452 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d890, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7540 p hg
    simpa only [d890, d1452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d890, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6546 p hg
    simpa only [d890, d1452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7542 (p : Pattern) (guard : d4670 p = 1) : d891 p ≤ (0 : Int) + d1456 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d891, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7541 p hg
    simpa only [d891, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d891, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7524 p hg
    simpa only [d891, d1456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7543 (p : Pattern) (guard : d4670 p = 1) : d892 p ≤ (0 : Int) + d1463 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d892, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7538 p hg
    simpa only [d892, d1463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d892, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7542 p hg
    simpa only [d892, d1463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7544 (p : Pattern) (guard : d4670 p = 1) : d893 p ≤ (0 : Int) + d1464 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d893, d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7542 p hg
    simpa only [d893, d1464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d893, d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6484 p hg
    simpa only [d893, d1464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7545 (p : Pattern) (guard : d4670 p = 1) : d894 p ≤ (0 : Int) + d1465 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d894, d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7543 p hg
    simpa only [d894, d1465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d894, d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7544 p hg
    simpa only [d894, d1465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7546 (p : Pattern) (guard : d4670 p = 1) : d895 p ≤ (0 : Int) + d1466 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d895, d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7532 p hg
    simpa only [d895, d1466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d895, d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7545 p hg
    simpa only [d895, d1466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7547 (p : Pattern) (guard : d4670 p = 1) : d896 p ≤ (0 : Int) + d1467 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d896, d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7474 p hg
    simpa only [d896, d1467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d896, d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7546 p hg
    simpa only [d896, d1467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7548 (p : Pattern) (guard : d4670 p = 1) : d897 p ≤ (0 : Int) + d1468 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d897, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7501 p hg
    simpa only [d897, d1468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d897, d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7547 p hg
    simpa only [d897, d1468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7549 (p : Pattern) (guard : d0 p = 1) : d79 p ≤ (0 : Int) + d21 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7550 (p : Pattern) (guard : d4395 p = 1) : d188 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d188, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4395, d188, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d188, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7549 p hg
    simpa only [d4395, d188, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7551 (p : Pattern) (guard : d4670 p = 1) : d898 p ≤ (0 : Int) + d1412 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d898, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7550 p hg
    simpa only [d4670, d898, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d898, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7467 p hg
    simpa only [d4670, d898, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7552 (p : Pattern) (guard : d0 p = 1) : d194 p ≤ (0 : Int) + d63 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7553 (p : Pattern) (guard : d4395 p = 1) : d899 p ≤ (0 : Int) + d1413 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d899, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4395, d899, d1413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d899, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7552 p hg
    simpa only [d4395, d899, d1413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7554 (p : Pattern) (guard : d4670 p = 1) : d900 p ≤ (0 : Int) + d1414 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d900, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7553 p hg
    simpa only [d4670, d900, d1414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d900, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4670, d900, d1414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7555 (p : Pattern) (guard : d4670 p = 1) : d901 p ≤ (0 : Int) + d1415 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d901, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7551 p hg
    simpa only [d901, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d901, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7554 p hg
    simpa only [d901, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7556 (p : Pattern) (guard : d0 p = 1) : d198 p ≤ (0 : Int) + d1181 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7557 (p : Pattern) (guard : d4395 p = 1) : d199 p ≤ (0 : Int) + d1469 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d199, d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4395, d199, d1469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d199, d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7556 p hg
    simpa only [d4395, d199, d1469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7558 (p : Pattern) (guard : d4670 p = 1) : d902 p ≤ (0 : Int) + d1470 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d902, d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7557 p hg
    simpa only [d4670, d902, d1470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d902, d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7440 p hg
    simpa only [d4670, d902, d1470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7559 (p : Pattern) (guard : d4670 p = 1) : d905 p ≤ (0 : Int) + d1471 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d905, d1471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7558 p hg
    simpa only [d905, d1471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d905, d1471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6605 p hg
    simpa only [d905, d1471, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
