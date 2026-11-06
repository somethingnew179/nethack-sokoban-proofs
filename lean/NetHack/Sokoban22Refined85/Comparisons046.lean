/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons045
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare6440 (p : Pattern) (guard : d4670 p = 1) : d816 p ≤ (0 : Int) + d980 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d816, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6439 p hg
    simpa only [d816, d980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d816, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6424 p hg
    simpa only [d816, d980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6441 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d371 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6442 (p : Pattern) (guard : d4395 p = 1) : d56 p ≤ (0 : Int) + d981 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d56, d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d56, d981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d56, d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6441 p hg
    simpa only [d4395, d56, d981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6443 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (0 : Int) + d972 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6444 (p : Pattern) (guard : d4670 p = 1) : d817 p ≤ (0 : Int) + d982 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d817, d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6442 p hg
    simpa only [d4670, d817, d982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d817, d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6443 p hg
    simpa only [d4670, d817, d982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6445 (p : Pattern) (guard : d4670 p = 1) : d818 p ≤ (0 : Int) + d983 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d818, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6444 p hg
    simpa only [d818, d983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d818, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6433 p hg
    simpa only [d818, d983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6446 (p : Pattern) (guard : d4670 p = 1) : d819 p ≤ (0 : Int) + d984 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d819, d984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6440 p hg
    simpa only [d819, d984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d819, d984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6445 p hg
    simpa only [d819, d984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6447 (p : Pattern) (guard : d1 p = 1) : d89 p ≤ (0 : Int) + d89 p := by
  omega
theorem compare6448 (p : Pattern) (guard : d4395 p = 1) : d90 p ≤ (0 : Int) + d985 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d90, d985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6447 p hg
    simpa only [d4395, d90, d985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d90, d985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d4395, d90, d985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6449 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d91 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6450 (p : Pattern) (guard : d4670 p = 1) : d820 p ≤ (0 : Int) + d986 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d820, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6448 p hg
    simpa only [d4670, d820, d986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d820, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6449 p hg
    simpa only [d4670, d820, d986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6451 (p : Pattern) (guard : d4670 p = 1) : d93 p ≤ (0 : Int) + d93 p := by
  omega
theorem compare6452 (p : Pattern) (guard : d4670 p = 1) : d821 p ≤ (0 : Int) + d987 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d821, d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6450 p hg
    simpa only [d821, d987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d821, d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6451 p hg
    simpa only [d821, d987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6453 (p : Pattern) (guard : d4670 p = 1) : d95 p ≤ (0 : Int) + d95 p := by
  omega
theorem compare6454 (p : Pattern) (guard : d4670 p = 1) : d822 p ≤ (0 : Int) + d988 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d822, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6452 p hg
    simpa only [d822, d988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d822, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6453 p hg
    simpa only [d822, d988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6455 (p : Pattern) (guard : d4670 p = 1) : d823 p ≤ (0 : Int) + d989 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d823, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6446 p hg
    simpa only [d823, d989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d823, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6454 p hg
    simpa only [d823, d989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6456 (p : Pattern) (guard : d4670 p = 1) : d824 p ≤ (0 : Int) + d990 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d824, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6436 p hg
    simpa only [d824, d990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d824, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6455 p hg
    simpa only [d824, d990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6457 (p : Pattern) (guard : d4395 p = 1) : d22 p ≤ (0 : Int) + d991 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d22, d991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4395, d22, d991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d22, d991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4255 p hg
    simpa only [d4395, d22, d991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6458 (p : Pattern) (guard : d0 p = 1) : d390 p ≤ (0 : Int) + d992 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6459 (p : Pattern) (guard : d4670 p = 1) : d825 p ≤ (0 : Int) + d993 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d825, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6457 p hg
    simpa only [d4670, d825, d993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d825, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6458 p hg
    simpa only [d4670, d825, d993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6460 (p : Pattern) (guard : d4395 p = 1) : d791 p ≤ (0 : Int) + d994 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d791, d994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4395, d791, d994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d791, d994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6422 p hg
    simpa only [d4395, d791, d994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6461 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d954 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6462 (p : Pattern) (guard : d4670 p = 1) : d826 p ≤ (0 : Int) + d995 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d826, d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6460 p hg
    simpa only [d4670, d826, d995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d826, d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6461 p hg
    simpa only [d4670, d826, d995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6463 (p : Pattern) (guard : d4670 p = 1) : d827 p ≤ (0 : Int) + d996 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d827, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6459 p hg
    simpa only [d827, d996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d827, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6462 p hg
    simpa only [d827, d996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6464 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d361 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6465 (p : Pattern) (guard : d4395 p = 1) : d56 p ≤ (0 : Int) + d997 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d56, d997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d56, d997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d56, d997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6464 p hg
    simpa only [d4395, d56, d997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6466 (p : Pattern) (guard : d0 p = 1) : d394 p ≤ (0 : Int) + d960 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6467 (p : Pattern) (guard : d4670 p = 1) : d828 p ≤ (0 : Int) + d998 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d828, d998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6465 p hg
    simpa only [d4670, d828, d998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d828, d998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6466 p hg
    simpa only [d4670, d828, d998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6468 (p : Pattern) (guard : d4670 p = 1) : d829 p ≤ (0 : Int) + d999 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d829, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6467 p hg
    simpa only [d829, d999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d829, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6416 p hg
    simpa only [d829, d999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6469 (p : Pattern) (guard : d4670 p = 1) : d830 p ≤ (0 : Int) + d1000 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d830, d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6463 p hg
    simpa only [d830, d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d830, d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6468 p hg
    simpa only [d830, d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6470 (p : Pattern) (guard : d4395 p = 1) : d22 p ≤ (0 : Int) + d1001 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d22, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4395, d22, d1001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d22, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4265 p hg
    simpa only [d4395, d22, d1001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6471 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d966 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6472 (p : Pattern) (guard : d4670 p = 1) : d831 p ≤ (0 : Int) + d1002 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d831, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6470 p hg
    simpa only [d4670, d831, d1002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d831, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6471 p hg
    simpa only [d4670, d831, d1002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6473 (p : Pattern) (guard : d4670 p = 1) : d832 p ≤ (0 : Int) + d1003 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d832, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6472 p hg
    simpa only [d832, d1003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d832, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6424 p hg
    simpa only [d832, d1003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6474 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6475 (p : Pattern) (guard : d4395 p = 1) : d56 p ≤ (0 : Int) + d966 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d56, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d56, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d56, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6474 p hg
    simpa only [d4395, d56, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6476 (p : Pattern) (guard : d4670 p = 1) : d807 p ≤ (0 : Int) + d1004 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d807, d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6475 p hg
    simpa only [d4670, d807, d1004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d807, d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6428 p hg
    simpa only [d4670, d807, d1004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6477 (p : Pattern) (guard : d4670 p = 1) : d812 p ≤ (0 : Int) + d1005 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d812, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6476 p hg
    simpa only [d812, d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d812, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6433 p hg
    simpa only [d812, d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6478 (p : Pattern) (guard : d4670 p = 1) : d833 p ≤ (0 : Int) + d1006 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d833, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6473 p hg
    simpa only [d833, d1006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d833, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6477 p hg
    simpa only [d833, d1006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6479 (p : Pattern) (guard : d4670 p = 1) : d834 p ≤ (0 : Int) + d1007 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d834, d1007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6469 p hg
    simpa only [d834, d1007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d834, d1007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6478 p hg
    simpa only [d834, d1007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6480 (p : Pattern) (guard : d4395 p = 1) : d22 p ≤ (0 : Int) + d1008 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d22, d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4395, d22, d1008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d22, d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4272 p hg
    simpa only [d4395, d22, d1008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6481 (p : Pattern) (guard : d4670 p = 1) : d831 p ≤ (0 : Int) + d1009 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d831, d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6480 p hg
    simpa only [d4670, d831, d1009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d831, d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6471 p hg
    simpa only [d4670, d831, d1009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6482 (p : Pattern) (guard : d4670 p = 1) : d832 p ≤ (0 : Int) + d1010 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d832, d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6481 p hg
    simpa only [d832, d1010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d832, d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6424 p hg
    simpa only [d832, d1010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6483 (p : Pattern) (guard : d4670 p = 1) : d833 p ≤ (0 : Int) + d1011 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d833, d1011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6482 p hg
    simpa only [d833, d1011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d833, d1011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6477 p hg
    simpa only [d833, d1011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6484 (p : Pattern) (guard : d4670 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare6485 (p : Pattern) (guard : d4670 p = 1) : d835 p ≤ (0 : Int) + d1012 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d835, d1012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6483 p hg
    simpa only [d835, d1012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d835, d1012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6484 p hg
    simpa only [d835, d1012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6486 (p : Pattern) (guard : d4670 p = 1) : d836 p ≤ (0 : Int) + d1013 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d836, d1013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6479 p hg
    simpa only [d836, d1013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d836, d1013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6485 p hg
    simpa only [d836, d1013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6487 (p : Pattern) (guard : d4670 p = 1) : d837 p ≤ (0 : Int) + d1014 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d837, d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6456 p hg
    simpa only [d837, d1014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d837, d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6486 p hg
    simpa only [d837, d1014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6488 (p : Pattern) (guard : d4395 p = 1) : d22 p ≤ (0 : Int) + d1015 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d22, d1015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4395, d22, d1015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d22, d1015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4282 p hg
    simpa only [d4395, d22, d1015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6489 (p : Pattern) (guard : d0 p = 1) : d372 p ≤ (0 : Int) + d1016 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6490 (p : Pattern) (guard : d4670 p = 1) : d838 p ≤ (0 : Int) + d1017 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d838, d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6488 p hg
    simpa only [d4670, d838, d1017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d838, d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6489 p hg
    simpa only [d4670, d838, d1017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6491 (p : Pattern) (guard : d0 p = 1) : d79 p ≤ (0 : Int) + d374 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6492 (p : Pattern) (guard : d4395 p = 1) : d791 p ≤ (0 : Int) + d1018 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d791, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4395, d791, d1018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d791, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6491 p hg
    simpa only [d4395, d791, d1018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6493 (p : Pattern) (guard : d4670 p = 1) : d826 p ≤ (0 : Int) + d1019 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d826, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6492 p hg
    simpa only [d4670, d826, d1019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d826, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6461 p hg
    simpa only [d4670, d826, d1019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6494 (p : Pattern) (guard : d4670 p = 1) : d839 p ≤ (0 : Int) + d1020 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d839, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6490 p hg
    simpa only [d839, d1020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d839, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6493 p hg
    simpa only [d839, d1020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6495 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d386 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6496 (p : Pattern) (guard : d4395 p = 1) : d56 p ≤ (0 : Int) + d1021 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d56, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d56, d1021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d56, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6495 p hg
    simpa only [d4395, d56, d1021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6497 (p : Pattern) (guard : d0 p = 1) : d390 p ≤ (0 : Int) + d960 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6498 (p : Pattern) (guard : d4670 p = 1) : d840 p ≤ (0 : Int) + d1022 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d840, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6496 p hg
    simpa only [d4670, d840, d1022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d840, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6497 p hg
    simpa only [d4670, d840, d1022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6499 (p : Pattern) (guard : d4670 p = 1) : d841 p ≤ (0 : Int) + d1023 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d841, d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6498 p hg
    simpa only [d841, d1023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d841, d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6416 p hg
    simpa only [d841, d1023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6500 (p : Pattern) (guard : d4670 p = 1) : d842 p ≤ (0 : Int) + d1024 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d842, d1024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6494 p hg
    simpa only [d842, d1024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d842, d1024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6499 p hg
    simpa only [d842, d1024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6501 (p : Pattern) (guard : d4395 p = 1) : d22 p ≤ (0 : Int) + d1025 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d22, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4395, d22, d1025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d22, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4293 p hg
    simpa only [d4395, d22, d1025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6502 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (0 : Int) + d966 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6503 (p : Pattern) (guard : d4670 p = 1) : d843 p ≤ (0 : Int) + d1026 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d843, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6501 p hg
    simpa only [d4670, d843, d1026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d843, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6502 p hg
    simpa only [d4670, d843, d1026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6504 (p : Pattern) (guard : d4670 p = 1) : d844 p ≤ (0 : Int) + d1027 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d844, d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6503 p hg
    simpa only [d844, d1027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d844, d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6424 p hg
    simpa only [d844, d1027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6505 (p : Pattern) (guard : d4670 p = 1) : d845 p ≤ (0 : Int) + d1028 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d845, d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6504 p hg
    simpa only [d845, d1028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d845, d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6477 p hg
    simpa only [d845, d1028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6506 (p : Pattern) (guard : d4670 p = 1) : d846 p ≤ (0 : Int) + d1029 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d846, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6500 p hg
    simpa only [d846, d1029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d846, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6505 p hg
    simpa only [d846, d1029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6507 (p : Pattern) (guard : d4670 p = 1) : d847 p ≤ (0 : Int) + d1030 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d847, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6435 p hg
    simpa only [d847, d1030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d847, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6454 p hg
    simpa only [d847, d1030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6508 (p : Pattern) (guard : d4670 p = 1) : d848 p ≤ (0 : Int) + d1031 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d848, d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6506 p hg
    simpa only [d848, d1031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d848, d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6507 p hg
    simpa only [d848, d1031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6509 (p : Pattern) (guard : d0 p = 1) : d403 p ≤ (0 : Int) + d992 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6510 (p : Pattern) (guard : d4670 p = 1) : d815 p ≤ (0 : Int) + d1032 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d815, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6437 p hg
    simpa only [d4670, d815, d1032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d815, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6509 p hg
    simpa only [d4670, d815, d1032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6511 (p : Pattern) (guard : d4670 p = 1) : d849 p ≤ (0 : Int) + d1033 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d849, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6510 p hg
    simpa only [d849, d1033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d849, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6462 p hg
    simpa only [d849, d1033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6512 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (0 : Int) + d960 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6513 (p : Pattern) (guard : d4670 p = 1) : d817 p ≤ (0 : Int) + d1034 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d817, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6442 p hg
    simpa only [d4670, d817, d1034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d817, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6512 p hg
    simpa only [d4670, d817, d1034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6514 (p : Pattern) (guard : d4670 p = 1) : d850 p ≤ (0 : Int) + d1035 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d850, d1035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6513 p hg
    simpa only [d850, d1035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d850, d1035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6416 p hg
    simpa only [d850, d1035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6515 (p : Pattern) (guard : d4670 p = 1) : d851 p ≤ (0 : Int) + d1036 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d851, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6511 p hg
    simpa only [d851, d1036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d851, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6514 p hg
    simpa only [d851, d1036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6516 (p : Pattern) (guard : d4670 p = 1) : d852 p ≤ (0 : Int) + d1037 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d852, d1037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6515 p hg
    simpa only [d852, d1037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d852, d1037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6478 p hg
    simpa only [d852, d1037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6517 (p : Pattern) (guard : d4670 p = 1) : d835 p ≤ (0 : Int) + d1038 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d835, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6478 p hg
    simpa only [d835, d1038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d835, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6484 p hg
    simpa only [d835, d1038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6518 (p : Pattern) (guard : d4670 p = 1) : d853 p ≤ (0 : Int) + d1039 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d853, d1039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6516 p hg
    simpa only [d853, d1039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d853, d1039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6517 p hg
    simpa only [d853, d1039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6519 (p : Pattern) (guard : d4670 p = 1) : d854 p ≤ (0 : Int) + d1040 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d854, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6508 p hg
    simpa only [d854, d1040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d854, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6518 p hg
    simpa only [d854, d1040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6520 (p : Pattern) (guard : d4670 p = 1) : d855 p ≤ (0 : Int) + d1041 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d855, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6487 p hg
    simpa only [d855, d1041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d855, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6519 p hg
    simpa only [d855, d1041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6521 (p : Pattern) (guard : d4395 p = 1) : d111 p ≤ (0 : Int) + d1042 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d111, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4395, d111, d1042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d111, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4315 p hg
    simpa only [d4395, d111, d1042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6522 (p : Pattern) (guard : d0 p = 1) : d372 p ≤ (0 : Int) + d1044 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6523 (p : Pattern) (guard : d4670 p = 1) : d856 p ≤ (0 : Int) + d1045 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d856, d1045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6521 p hg
    simpa only [d4670, d856, d1045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d856, d1045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6522 p hg
    simpa only [d4670, d856, d1045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6524 (p : Pattern) (guard : d0 p = 1) : d149 p ≤ (0 : Int) + d374 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6525 (p : Pattern) (guard : d4395 p = 1) : d857 p ≤ (0 : Int) + d1046 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d857, d1046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3757 p hg
    simpa only [d4395, d857, d1046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d857, d1046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6524 p hg
    simpa only [d4395, d857, d1046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6526 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1047 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6527 (p : Pattern) (guard : d4670 p = 1) : d858 p ≤ (0 : Int) + d1048 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d858, d1048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6525 p hg
    simpa only [d4670, d858, d1048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d858, d1048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6526 p hg
    simpa only [d4670, d858, d1048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6528 (p : Pattern) (guard : d4670 p = 1) : d859 p ≤ (0 : Int) + d1049 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d859, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6523 p hg
    simpa only [d859, d1049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d859, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6527 p hg
    simpa only [d859, d1049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6529 (p : Pattern) (guard : d1 p = 1) : d133 p ≤ (0 : Int) + d133 p := by
  omega
theorem compare6530 (p : Pattern) (guard : d0 p = 1) : d134 p ≤ (0 : Int) + d386 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6531 (p : Pattern) (guard : d4395 p = 1) : d135 p ≤ (0 : Int) + d1050 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d135, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d135, d1050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d135, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6530 p hg
    simpa only [d4395, d135, d1050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6532 (p : Pattern) (guard : d0 p = 1) : d390 p ≤ (0 : Int) + d1051 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6533 (p : Pattern) (guard : d4670 p = 1) : d860 p ≤ (0 : Int) + d1052 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d860, d1052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6531 p hg
    simpa only [d4670, d860, d1052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d860, d1052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6532 p hg
    simpa only [d4670, d860, d1052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6534 (p : Pattern) (guard : d1 p = 1) : d862 p ≤ (0 : Int) + d862 p := by
  omega
theorem compare6535 (p : Pattern) (guard : d0 p = 1) : d863 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6536 (p : Pattern) (guard : d4395 p = 1) : d864 p ≤ (0 : Int) + d1051 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d864, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6534 p hg
    simpa only [d4395, d864, d1051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d864, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6535 p hg
    simpa only [d4395, d864, d1051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6537 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1054 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6538 (p : Pattern) (guard : d4670 p = 1) : d865 p ≤ (0 : Int) + d1055 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d865, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6536 p hg
    simpa only [d4670, d865, d1055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d865, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6537 p hg
    simpa only [d4670, d865, d1055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6539 (p : Pattern) (guard : d4670 p = 1) : d866 p ≤ (0 : Int) + d1056 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d866, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6533 p hg
    simpa only [d866, d1056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d866, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6538 p hg
    simpa only [d866, d1056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6540 (p : Pattern) (guard : d4670 p = 1) : d867 p ≤ (0 : Int) + d1057 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d867, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6528 p hg
    simpa only [d867, d1057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d867, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6539 p hg
    simpa only [d867, d1057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6541 (p : Pattern) (guard : d4395 p = 1) : d111 p ≤ (0 : Int) + d1058 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d111, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4395, d111, d1058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d111, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4328 p hg
    simpa only [d4395, d111, d1058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6542 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (0 : Int) + d1059 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6543 (p : Pattern) (guard : d4670 p = 1) : d868 p ≤ (0 : Int) + d1060 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d868, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6541 p hg
    simpa only [d4670, d868, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d868, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6542 p hg
    simpa only [d4670, d868, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6544 (p : Pattern) (guard : d0 p = 1) : d149 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6545 (p : Pattern) (guard : d4395 p = 1) : d869 p ≤ (0 : Int) + d1061 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d869, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4395, d869, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d869, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6544 p hg
    simpa only [d4395, d869, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6546 (p : Pattern) (guard : d4670 p = 1) : d870 p ≤ (0 : Int) + d1062 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d870, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6545 p hg
    simpa only [d4670, d870, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d870, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4670, d870, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6547 (p : Pattern) (guard : d4670 p = 1) : d871 p ≤ (0 : Int) + d1063 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d871, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6543 p hg
    simpa only [d871, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d871, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6546 p hg
    simpa only [d871, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6548 (p : Pattern) (guard : d0 p = 1) : d134 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6549 (p : Pattern) (guard : d4395 p = 1) : d135 p ≤ (0 : Int) + d1059 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d135, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d135, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d135, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6548 p hg
    simpa only [d4395, d135, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6550 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1064 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6551 (p : Pattern) (guard : d4670 p = 1) : d872 p ≤ (0 : Int) + d1065 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d872, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6549 p hg
    simpa only [d4670, d872, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d872, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6550 p hg
    simpa only [d4670, d872, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6552 (p : Pattern) (guard : d1 p = 1) : d873 p ≤ (0 : Int) + d873 p := by
  omega
theorem compare6553 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6554 (p : Pattern) (guard : d4395 p = 1) : d874 p ≤ (0 : Int) + d1064 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d874, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6552 p hg
    simpa only [d4395, d874, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d874, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6553 p hg
    simpa only [d4395, d874, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6555 (p : Pattern) (guard : d4670 p = 1) : d875 p ≤ (0 : Int) + d1066 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d875, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6554 p hg
    simpa only [d4670, d875, d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d875, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4670, d875, d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6556 (p : Pattern) (guard : d4670 p = 1) : d876 p ≤ (0 : Int) + d1067 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d876, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6551 p hg
    simpa only [d876, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d876, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6555 p hg
    simpa only [d876, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6557 (p : Pattern) (guard : d4670 p = 1) : d877 p ≤ (0 : Int) + d1068 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d877, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6547 p hg
    simpa only [d877, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d877, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6556 p hg
    simpa only [d877, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6558 (p : Pattern) (guard : d4670 p = 1) : d878 p ≤ (0 : Int) + d1069 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d878, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6540 p hg
    simpa only [d878, d1069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d878, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6557 p hg
    simpa only [d878, d1069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6559 (p : Pattern) (guard : d4395 p = 1) : d111 p ≤ (0 : Int) + d1070 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d111, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4395, d111, d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d111, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4339 p hg
    simpa only [d4395, d111, d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6560 (p : Pattern) (guard : d0 p = 1) : d394 p ≤ (0 : Int) + d1059 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6561 (p : Pattern) (guard : d4670 p = 1) : d879 p ≤ (0 : Int) + d1071 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d879, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6559 p hg
    simpa only [d4670, d879, d1071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d879, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6560 p hg
    simpa only [d4670, d879, d1071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6562 (p : Pattern) (guard : d4670 p = 1) : d880 p ≤ (0 : Int) + d1072 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d880, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6561 p hg
    simpa only [d880, d1072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d880, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6546 p hg
    simpa only [d880, d1072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6563 (p : Pattern) (guard : d0 p = 1) : d134 p ≤ (0 : Int) + d374 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6564 (p : Pattern) (guard : d4395 p = 1) : d135 p ≤ (0 : Int) + d1073 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d135, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d135, d1073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d135, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6563 p hg
    simpa only [d4395, d135, d1073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6565 (p : Pattern) (guard : d4670 p = 1) : d872 p ≤ (0 : Int) + d1074 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d872, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6564 p hg
    simpa only [d4670, d872, d1074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d872, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6550 p hg
    simpa only [d4670, d872, d1074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6566 (p : Pattern) (guard : d4670 p = 1) : d876 p ≤ (0 : Int) + d1075 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d876, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6565 p hg
    simpa only [d876, d1075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d876, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6555 p hg
    simpa only [d876, d1075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6567 (p : Pattern) (guard : d4670 p = 1) : d881 p ≤ (0 : Int) + d1076 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d881, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6562 p hg
    simpa only [d881, d1076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d881, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6566 p hg
    simpa only [d881, d1076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6568 (p : Pattern) (guard : d4670 p = 1) : d162 p ≤ (0 : Int) + d162 p := by
  omega
theorem compare6569 (p : Pattern) (guard : d4670 p = 1) : d882 p ≤ (0 : Int) + d1077 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d882, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6567 p hg
    simpa only [d882, d1077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d882, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6568 p hg
    simpa only [d882, d1077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6570 (p : Pattern) (guard : d4670 p = 1) : d883 p ≤ (0 : Int) + d1078 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d883, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6558 p hg
    simpa only [d883, d1078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d883, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6569 p hg
    simpa only [d883, d1078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6571 (p : Pattern) (guard : d4395 p = 1) : d111 p ≤ (0 : Int) + d1079 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d111, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4395, d111, d1079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d111, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4348 p hg
    simpa only [d4395, d111, d1079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6572 (p : Pattern) (guard : d0 p = 1) : d403 p ≤ (0 : Int) + d1080 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6573 (p : Pattern) (guard : d4670 p = 1) : d884 p ≤ (0 : Int) + d1081 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d884, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6571 p hg
    simpa only [d4670, d884, d1081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d884, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6572 p hg
    simpa only [d4670, d884, d1081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6574 (p : Pattern) (guard : d4395 p = 1) : d857 p ≤ (0 : Int) + d1082 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d857, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3757 p hg
    simpa only [d4395, d857, d1082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d857, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6544 p hg
    simpa only [d4395, d857, d1082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6575 (p : Pattern) (guard : d4670 p = 1) : d858 p ≤ (0 : Int) + d1083 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d858, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6574 p hg
    simpa only [d4670, d858, d1083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d858, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6526 p hg
    simpa only [d4670, d858, d1083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6576 (p : Pattern) (guard : d4670 p = 1) : d885 p ≤ (0 : Int) + d1084 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d885, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6573 p hg
    simpa only [d885, d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d885, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6575 p hg
    simpa only [d885, d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6577 (p : Pattern) (guard : d0 p = 1) : d134 p ≤ (0 : Int) + d371 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6578 (p : Pattern) (guard : d4395 p = 1) : d135 p ≤ (0 : Int) + d1085 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d135, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d135, d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d135, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6577 p hg
    simpa only [d4395, d135, d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6579 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (0 : Int) + d1051 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
