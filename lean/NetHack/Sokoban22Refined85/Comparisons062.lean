/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons061
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare8680 (p : Pattern) (guard : d4395 p = 1) : d960 p ≤ (0 : Int) + d799 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d960, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6412 p hg
    simpa only [d4395, d960, d799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d960, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8679 p hg
    simpa only [d4395, d960, d799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8681 (p : Pattern) (guard : d0 p = 1) : d961 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8682 (p : Pattern) (guard : d4670 p = 1) : d962 p ≤ (0 : Int) + d800 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d962, d800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8680 p hg
    simpa only [d4670, d962, d800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d962, d800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8681 p hg
    simpa only [d4670, d962, d800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8683 (p : Pattern) (guard : d4670 p = 1) : d963 p ≤ (0 : Int) + d801 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d963, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8678 p hg
    simpa only [d963, d801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d963, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8682 p hg
    simpa only [d963, d801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8684 (p : Pattern) (guard : d4670 p = 1) : d964 p ≤ (0 : Int) + d802 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d964, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8674 p hg
    simpa only [d964, d802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d964, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8683 p hg
    simpa only [d964, d802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8685 (p : Pattern) (guard : d0 p = 1) : d966 p ≤ (0 : Int) + d394 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8686 (p : Pattern) (guard : d4670 p = 1) : d967 p ≤ (0 : Int) + d803 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d967, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7811 p hg
    simpa only [d4670, d967, d803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d967, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8685 p hg
    simpa only [d4670, d967, d803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8687 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d79 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8688 (p : Pattern) (guard : d4395 p = 1) : d968 p ≤ (0 : Int) + d804 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d968, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4395, d968, d804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d968, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8687 p hg
    simpa only [d4395, d968, d804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8689 (p : Pattern) (guard : d4670 p = 1) : d969 p ≤ (0 : Int) + d805 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d969, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8688 p hg
    simpa only [d4670, d969, d805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d969, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4670, d969, d805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8690 (p : Pattern) (guard : d4670 p = 1) : d970 p ≤ (0 : Int) + d806 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d970, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8686 p hg
    simpa only [d970, d806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d970, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8689 p hg
    simpa only [d970, d806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8691 (p : Pattern) (guard : d0 p = 1) : d374 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8692 (p : Pattern) (guard : d4395 p = 1) : d971 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d971, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d971, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d971, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8691 p hg
    simpa only [d4395, d971, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8693 (p : Pattern) (guard : d0 p = 1) : d972 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8694 (p : Pattern) (guard : d4670 p = 1) : d973 p ≤ (0 : Int) + d807 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d973, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8692 p hg
    simpa only [d4670, d973, d807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d973, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8693 p hg
    simpa only [d4670, d973, d807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8695 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d809 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8696 (p : Pattern) (guard : d4395 p = 1) : d972 p ≤ (0 : Int) + d810 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d972, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6430 p hg
    simpa only [d4395, d972, d810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d972, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8695 p hg
    simpa only [d4395, d972, d810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8697 (p : Pattern) (guard : d4670 p = 1) : d974 p ≤ (0 : Int) + d811 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d974, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8696 p hg
    simpa only [d4670, d974, d811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d974, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4670, d974, d811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8698 (p : Pattern) (guard : d4670 p = 1) : d975 p ≤ (0 : Int) + d812 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d975, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8694 p hg
    simpa only [d975, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d975, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8697 p hg
    simpa only [d975, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8699 (p : Pattern) (guard : d4670 p = 1) : d976 p ≤ (0 : Int) + d813 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d976, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8690 p hg
    simpa only [d976, d813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d976, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8698 p hg
    simpa only [d976, d813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8700 (p : Pattern) (guard : d4670 p = 1) : d977 p ≤ (0 : Int) + d814 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d977, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8684 p hg
    simpa only [d977, d814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d977, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8699 p hg
    simpa only [d977, d814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8701 (p : Pattern) (guard : d0 p = 1) : d966 p ≤ (0 : Int) + d403 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8702 (p : Pattern) (guard : d4670 p = 1) : d979 p ≤ (0 : Int) + d815 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d979, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7829 p hg
    simpa only [d4670, d979, d815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d979, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8701 p hg
    simpa only [d4670, d979, d815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8703 (p : Pattern) (guard : d4670 p = 1) : d980 p ≤ (0 : Int) + d816 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d980, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8702 p hg
    simpa only [d980, d816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d980, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8689 p hg
    simpa only [d980, d816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8704 (p : Pattern) (guard : d0 p = 1) : d371 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8705 (p : Pattern) (guard : d4395 p = 1) : d981 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d981, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d981, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d981, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8704 p hg
    simpa only [d4395, d981, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8706 (p : Pattern) (guard : d0 p = 1) : d972 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8707 (p : Pattern) (guard : d4670 p = 1) : d982 p ≤ (0 : Int) + d817 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d982, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8705 p hg
    simpa only [d4670, d982, d817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d982, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8706 p hg
    simpa only [d4670, d982, d817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8708 (p : Pattern) (guard : d4670 p = 1) : d983 p ≤ (0 : Int) + d818 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d983, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8707 p hg
    simpa only [d983, d818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d983, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8697 p hg
    simpa only [d983, d818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8709 (p : Pattern) (guard : d4670 p = 1) : d984 p ≤ (0 : Int) + d819 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d984, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8703 p hg
    simpa only [d984, d819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d984, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8708 p hg
    simpa only [d984, d819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8710 (p : Pattern) (guard : d4670 p = 1) : d986 p ≤ (0 : Int) + d820 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d986, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7837 p hg
    simpa only [d4670, d986, d820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d986, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5894 p hg
    simpa only [d4670, d986, d820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8711 (p : Pattern) (guard : d4670 p = 1) : d987 p ≤ (0 : Int) + d821 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d987, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8710 p hg
    simpa only [d987, d821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d987, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6451 p hg
    simpa only [d987, d821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8712 (p : Pattern) (guard : d4670 p = 1) : d988 p ≤ (0 : Int) + d822 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d988, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8711 p hg
    simpa only [d988, d822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d988, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6453 p hg
    simpa only [d988, d822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8713 (p : Pattern) (guard : d4670 p = 1) : d989 p ≤ (0 : Int) + d823 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d989, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8709 p hg
    simpa only [d989, d823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d989, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8712 p hg
    simpa only [d989, d823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8714 (p : Pattern) (guard : d4670 p = 1) : d990 p ≤ (0 : Int) + d824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d990, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8700 p hg
    simpa only [d990, d824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d990, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8713 p hg
    simpa only [d990, d824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8715 (p : Pattern) (guard : d0 p = 1) : d992 p ≤ (0 : Int) + d390 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8716 (p : Pattern) (guard : d4670 p = 1) : d993 p ≤ (0 : Int) + d825 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d993, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7847 p hg
    simpa only [d4670, d993, d825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d993, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8715 p hg
    simpa only [d4670, d993, d825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8717 (p : Pattern) (guard : d4395 p = 1) : d994 p ≤ (0 : Int) + d791 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d994, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4395, d994, d791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d994, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8687 p hg
    simpa only [d4395, d994, d791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8718 (p : Pattern) (guard : d0 p = 1) : d954 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8719 (p : Pattern) (guard : d4670 p = 1) : d995 p ≤ (0 : Int) + d826 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d995, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8717 p hg
    simpa only [d4670, d995, d826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d995, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8718 p hg
    simpa only [d4670, d995, d826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8720 (p : Pattern) (guard : d4670 p = 1) : d996 p ≤ (0 : Int) + d827 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d996, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8716 p hg
    simpa only [d996, d827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d996, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8719 p hg
    simpa only [d996, d827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8721 (p : Pattern) (guard : d0 p = 1) : d361 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8722 (p : Pattern) (guard : d4395 p = 1) : d997 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d997, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d997, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d997, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8721 p hg
    simpa only [d4395, d997, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8723 (p : Pattern) (guard : d0 p = 1) : d960 p ≤ (0 : Int) + d394 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8724 (p : Pattern) (guard : d4670 p = 1) : d998 p ≤ (0 : Int) + d828 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d998, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8722 p hg
    simpa only [d4670, d998, d828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d998, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8723 p hg
    simpa only [d4670, d998, d828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8725 (p : Pattern) (guard : d4670 p = 1) : d999 p ≤ (0 : Int) + d829 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d999, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8724 p hg
    simpa only [d999, d829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d999, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8682 p hg
    simpa only [d999, d829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8726 (p : Pattern) (guard : d4670 p = 1) : d1000 p ≤ (0 : Int) + d830 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1000, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8720 p hg
    simpa only [d1000, d830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1000, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8725 p hg
    simpa only [d1000, d830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8727 (p : Pattern) (guard : d0 p = 1) : d966 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8728 (p : Pattern) (guard : d4670 p = 1) : d1002 p ≤ (0 : Int) + d831 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1002, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7861 p hg
    simpa only [d4670, d1002, d831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1002, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8727 p hg
    simpa only [d4670, d1002, d831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8729 (p : Pattern) (guard : d4670 p = 1) : d1003 p ≤ (0 : Int) + d832 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1003, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8728 p hg
    simpa only [d1003, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1003, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8689 p hg
    simpa only [d1003, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8730 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8731 (p : Pattern) (guard : d4395 p = 1) : d966 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d966, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d966, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d966, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8730 p hg
    simpa only [d4395, d966, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8732 (p : Pattern) (guard : d4670 p = 1) : d1004 p ≤ (0 : Int) + d807 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1004, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8731 p hg
    simpa only [d4670, d1004, d807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1004, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8693 p hg
    simpa only [d4670, d1004, d807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8733 (p : Pattern) (guard : d4670 p = 1) : d1005 p ≤ (0 : Int) + d812 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1005, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8732 p hg
    simpa only [d1005, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1005, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8697 p hg
    simpa only [d1005, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8734 (p : Pattern) (guard : d4670 p = 1) : d1006 p ≤ (0 : Int) + d833 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1006, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8729 p hg
    simpa only [d1006, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1006, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8733 p hg
    simpa only [d1006, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8735 (p : Pattern) (guard : d4670 p = 1) : d1007 p ≤ (0 : Int) + d834 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1007, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8726 p hg
    simpa only [d1007, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1007, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8734 p hg
    simpa only [d1007, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8736 (p : Pattern) (guard : d4670 p = 1) : d1009 p ≤ (0 : Int) + d831 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1009, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7871 p hg
    simpa only [d4670, d1009, d831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1009, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8727 p hg
    simpa only [d4670, d1009, d831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8737 (p : Pattern) (guard : d4670 p = 1) : d1010 p ≤ (0 : Int) + d832 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1010, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8736 p hg
    simpa only [d1010, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1010, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8689 p hg
    simpa only [d1010, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8738 (p : Pattern) (guard : d4670 p = 1) : d1011 p ≤ (0 : Int) + d833 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1011, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8737 p hg
    simpa only [d1011, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1011, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8733 p hg
    simpa only [d1011, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8739 (p : Pattern) (guard : d4670 p = 1) : d1012 p ≤ (0 : Int) + d835 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1012, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8738 p hg
    simpa only [d1012, d835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1012, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6484 p hg
    simpa only [d1012, d835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8740 (p : Pattern) (guard : d4670 p = 1) : d1013 p ≤ (0 : Int) + d836 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1013, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8735 p hg
    simpa only [d1013, d836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1013, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8739 p hg
    simpa only [d1013, d836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8741 (p : Pattern) (guard : d4670 p = 1) : d1014 p ≤ (0 : Int) + d837 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1014, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8714 p hg
    simpa only [d1014, d837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1014, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8740 p hg
    simpa only [d1014, d837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8742 (p : Pattern) (guard : d0 p = 1) : d1016 p ≤ (0 : Int) + d372 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8743 (p : Pattern) (guard : d4670 p = 1) : d1017 p ≤ (0 : Int) + d838 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1017, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7879 p hg
    simpa only [d4670, d1017, d838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1017, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8742 p hg
    simpa only [d4670, d1017, d838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8744 (p : Pattern) (guard : d0 p = 1) : d374 p ≤ (0 : Int) + d79 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8745 (p : Pattern) (guard : d4395 p = 1) : d1018 p ≤ (0 : Int) + d791 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1018, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4395, d1018, d791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1018, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8744 p hg
    simpa only [d4395, d1018, d791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8746 (p : Pattern) (guard : d4670 p = 1) : d1019 p ≤ (0 : Int) + d826 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1019, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8745 p hg
    simpa only [d4670, d1019, d826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1019, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8718 p hg
    simpa only [d4670, d1019, d826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8747 (p : Pattern) (guard : d4670 p = 1) : d1020 p ≤ (0 : Int) + d839 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1020, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8743 p hg
    simpa only [d1020, d839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1020, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8746 p hg
    simpa only [d1020, d839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8748 (p : Pattern) (guard : d0 p = 1) : d386 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8749 (p : Pattern) (guard : d4395 p = 1) : d1021 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1021, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d1021, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1021, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8748 p hg
    simpa only [d4395, d1021, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8750 (p : Pattern) (guard : d0 p = 1) : d960 p ≤ (0 : Int) + d390 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8751 (p : Pattern) (guard : d4670 p = 1) : d1022 p ≤ (0 : Int) + d840 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1022, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8749 p hg
    simpa only [d4670, d1022, d840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1022, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8750 p hg
    simpa only [d4670, d1022, d840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8752 (p : Pattern) (guard : d4670 p = 1) : d1023 p ≤ (0 : Int) + d841 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1023, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8751 p hg
    simpa only [d1023, d841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1023, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8682 p hg
    simpa only [d1023, d841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8753 (p : Pattern) (guard : d4670 p = 1) : d1024 p ≤ (0 : Int) + d842 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1024, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8747 p hg
    simpa only [d1024, d842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1024, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8752 p hg
    simpa only [d1024, d842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8754 (p : Pattern) (guard : d0 p = 1) : d966 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8755 (p : Pattern) (guard : d4670 p = 1) : d1026 p ≤ (0 : Int) + d843 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1026, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7893 p hg
    simpa only [d4670, d1026, d843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1026, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8754 p hg
    simpa only [d4670, d1026, d843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8756 (p : Pattern) (guard : d4670 p = 1) : d1027 p ≤ (0 : Int) + d844 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1027, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8755 p hg
    simpa only [d1027, d844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1027, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8689 p hg
    simpa only [d1027, d844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8757 (p : Pattern) (guard : d4670 p = 1) : d1028 p ≤ (0 : Int) + d845 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1028, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8756 p hg
    simpa only [d1028, d845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1028, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8733 p hg
    simpa only [d1028, d845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8758 (p : Pattern) (guard : d4670 p = 1) : d1029 p ≤ (0 : Int) + d846 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1029, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8753 p hg
    simpa only [d1029, d846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1029, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8757 p hg
    simpa only [d1029, d846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8759 (p : Pattern) (guard : d4670 p = 1) : d1030 p ≤ (0 : Int) + d847 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1030, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8699 p hg
    simpa only [d1030, d847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1030, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8712 p hg
    simpa only [d1030, d847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8760 (p : Pattern) (guard : d4670 p = 1) : d1031 p ≤ (0 : Int) + d848 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1031, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8758 p hg
    simpa only [d1031, d848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1031, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8759 p hg
    simpa only [d1031, d848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8761 (p : Pattern) (guard : d0 p = 1) : d992 p ≤ (0 : Int) + d403 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8762 (p : Pattern) (guard : d4670 p = 1) : d1032 p ≤ (0 : Int) + d815 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1032, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7829 p hg
    simpa only [d4670, d1032, d815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1032, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8761 p hg
    simpa only [d4670, d1032, d815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8763 (p : Pattern) (guard : d4670 p = 1) : d1033 p ≤ (0 : Int) + d849 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1033, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8762 p hg
    simpa only [d1033, d849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1033, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8719 p hg
    simpa only [d1033, d849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8764 (p : Pattern) (guard : d0 p = 1) : d960 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8765 (p : Pattern) (guard : d4670 p = 1) : d1034 p ≤ (0 : Int) + d817 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1034, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8705 p hg
    simpa only [d4670, d1034, d817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1034, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8764 p hg
    simpa only [d4670, d1034, d817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8766 (p : Pattern) (guard : d4670 p = 1) : d1035 p ≤ (0 : Int) + d850 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1035, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8765 p hg
    simpa only [d1035, d850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1035, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8682 p hg
    simpa only [d1035, d850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8767 (p : Pattern) (guard : d4670 p = 1) : d1036 p ≤ (0 : Int) + d851 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1036, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8763 p hg
    simpa only [d1036, d851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1036, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8766 p hg
    simpa only [d1036, d851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8768 (p : Pattern) (guard : d4670 p = 1) : d1037 p ≤ (0 : Int) + d852 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1037, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8767 p hg
    simpa only [d1037, d852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1037, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8734 p hg
    simpa only [d1037, d852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8769 (p : Pattern) (guard : d4670 p = 1) : d1038 p ≤ (0 : Int) + d835 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1038, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8734 p hg
    simpa only [d1038, d835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1038, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6484 p hg
    simpa only [d1038, d835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8770 (p : Pattern) (guard : d4670 p = 1) : d1039 p ≤ (0 : Int) + d853 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1039, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8768 p hg
    simpa only [d1039, d853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1039, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8769 p hg
    simpa only [d1039, d853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8771 (p : Pattern) (guard : d4670 p = 1) : d1040 p ≤ (0 : Int) + d854 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1040, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8760 p hg
    simpa only [d1040, d854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1040, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8770 p hg
    simpa only [d1040, d854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8772 (p : Pattern) (guard : d4670 p = 1) : d1041 p ≤ (0 : Int) + d855 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1041, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8741 p hg
    simpa only [d1041, d855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1041, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8771 p hg
    simpa only [d1041, d855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8773 (p : Pattern) (guard : d0 p = 1) : d1044 p ≤ (0 : Int) + d372 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8774 (p : Pattern) (guard : d4670 p = 1) : d1045 p ≤ (0 : Int) + d856 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1045, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7911 p hg
    simpa only [d4670, d1045, d856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1045, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8773 p hg
    simpa only [d4670, d1045, d856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8775 (p : Pattern) (guard : d0 p = 1) : d374 p ≤ (0 : Int) + d149 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8776 (p : Pattern) (guard : d4395 p = 1) : d1046 p ≤ (0 : Int) + d857 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1046, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3757 p hg
    simpa only [d4395, d1046, d857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1046, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8775 p hg
    simpa only [d4395, d1046, d857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8777 (p : Pattern) (guard : d0 p = 1) : d1047 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8778 (p : Pattern) (guard : d4670 p = 1) : d1048 p ≤ (0 : Int) + d858 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1048, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8776 p hg
    simpa only [d4670, d1048, d858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1048, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8777 p hg
    simpa only [d4670, d1048, d858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8779 (p : Pattern) (guard : d4670 p = 1) : d1049 p ≤ (0 : Int) + d859 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1049, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8774 p hg
    simpa only [d1049, d859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1049, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8778 p hg
    simpa only [d1049, d859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8780 (p : Pattern) (guard : d0 p = 1) : d386 p ≤ (0 : Int) + d134 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8781 (p : Pattern) (guard : d4395 p = 1) : d1050 p ≤ (0 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1050, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d1050, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1050, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8780 p hg
    simpa only [d4395, d1050, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8782 (p : Pattern) (guard : d0 p = 1) : d1051 p ≤ (0 : Int) + d390 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8783 (p : Pattern) (guard : d4670 p = 1) : d1052 p ≤ (0 : Int) + d860 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1052, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8781 p hg
    simpa only [d4670, d1052, d860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1052, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8782 p hg
    simpa only [d4670, d1052, d860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8784 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d863 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8785 (p : Pattern) (guard : d4395 p = 1) : d1051 p ≤ (0 : Int) + d864 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1051, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6534 p hg
    simpa only [d4395, d1051, d864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1051, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8784 p hg
    simpa only [d4395, d1051, d864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8786 (p : Pattern) (guard : d0 p = 1) : d1054 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8787 (p : Pattern) (guard : d4670 p = 1) : d1055 p ≤ (0 : Int) + d865 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1055, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8785 p hg
    simpa only [d4670, d1055, d865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1055, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8786 p hg
    simpa only [d4670, d1055, d865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8788 (p : Pattern) (guard : d4670 p = 1) : d1056 p ≤ (0 : Int) + d866 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1056, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8783 p hg
    simpa only [d1056, d866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1056, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8787 p hg
    simpa only [d1056, d866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8789 (p : Pattern) (guard : d4670 p = 1) : d1057 p ≤ (0 : Int) + d867 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1057, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8779 p hg
    simpa only [d1057, d867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1057, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8788 p hg
    simpa only [d1057, d867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8790 (p : Pattern) (guard : d0 p = 1) : d1059 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8791 (p : Pattern) (guard : d4670 p = 1) : d1060 p ≤ (0 : Int) + d868 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1060, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d4670, d1060, d868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1060, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8790 p hg
    simpa only [d4670, d1060, d868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8792 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d149 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8793 (p : Pattern) (guard : d4395 p = 1) : d1061 p ≤ (0 : Int) + d869 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1061, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4395, d1061, d869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1061, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8792 p hg
    simpa only [d4395, d1061, d869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8794 (p : Pattern) (guard : d4670 p = 1) : d1062 p ≤ (0 : Int) + d870 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1062, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8793 p hg
    simpa only [d4670, d1062, d870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1062, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4670, d1062, d870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8795 (p : Pattern) (guard : d4670 p = 1) : d1063 p ≤ (0 : Int) + d871 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1063, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8791 p hg
    simpa only [d1063, d871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1063, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8794 p hg
    simpa only [d1063, d871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8796 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d134 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8797 (p : Pattern) (guard : d4395 p = 1) : d1059 p ≤ (0 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1059, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d1059, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1059, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8796 p hg
    simpa only [d4395, d1059, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8798 (p : Pattern) (guard : d0 p = 1) : d1064 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8799 (p : Pattern) (guard : d4670 p = 1) : d1065 p ≤ (0 : Int) + d872 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1065, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8797 p hg
    simpa only [d4670, d1065, d872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1065, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8798 p hg
    simpa only [d4670, d1065, d872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8800 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d153 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8801 (p : Pattern) (guard : d4395 p = 1) : d1064 p ≤ (0 : Int) + d874 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1064, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6552 p hg
    simpa only [d4395, d1064, d874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1064, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8800 p hg
    simpa only [d4395, d1064, d874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8802 (p : Pattern) (guard : d4670 p = 1) : d1066 p ≤ (0 : Int) + d875 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1066, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8801 p hg
    simpa only [d4670, d1066, d875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1066, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4670, d1066, d875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8803 (p : Pattern) (guard : d4670 p = 1) : d1067 p ≤ (0 : Int) + d876 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1067, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8799 p hg
    simpa only [d1067, d876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1067, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8802 p hg
    simpa only [d1067, d876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8804 (p : Pattern) (guard : d4670 p = 1) : d1068 p ≤ (0 : Int) + d877 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1068, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8795 p hg
    simpa only [d1068, d877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1068, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8803 p hg
    simpa only [d1068, d877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8805 (p : Pattern) (guard : d4670 p = 1) : d1069 p ≤ (0 : Int) + d878 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1069, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8789 p hg
    simpa only [d1069, d878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1069, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8804 p hg
    simpa only [d1069, d878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8806 (p : Pattern) (guard : d0 p = 1) : d1059 p ≤ (0 : Int) + d394 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8807 (p : Pattern) (guard : d4670 p = 1) : d1071 p ≤ (0 : Int) + d879 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1071, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7949 p hg
    simpa only [d4670, d1071, d879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1071, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8806 p hg
    simpa only [d4670, d1071, d879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8808 (p : Pattern) (guard : d4670 p = 1) : d1072 p ≤ (0 : Int) + d880 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1072, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8807 p hg
    simpa only [d1072, d880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1072, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8794 p hg
    simpa only [d1072, d880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8809 (p : Pattern) (guard : d0 p = 1) : d374 p ≤ (0 : Int) + d134 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8810 (p : Pattern) (guard : d4395 p = 1) : d1073 p ≤ (0 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1073, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d1073, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1073, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8809 p hg
    simpa only [d4395, d1073, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8811 (p : Pattern) (guard : d4670 p = 1) : d1074 p ≤ (0 : Int) + d872 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1074, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8810 p hg
    simpa only [d4670, d1074, d872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1074, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8798 p hg
    simpa only [d4670, d1074, d872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8812 (p : Pattern) (guard : d4670 p = 1) : d1075 p ≤ (0 : Int) + d876 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1075, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8811 p hg
    simpa only [d1075, d876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1075, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8802 p hg
    simpa only [d1075, d876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8813 (p : Pattern) (guard : d4670 p = 1) : d1076 p ≤ (0 : Int) + d881 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1076, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8808 p hg
    simpa only [d1076, d881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1076, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8812 p hg
    simpa only [d1076, d881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8814 (p : Pattern) (guard : d4670 p = 1) : d1077 p ≤ (0 : Int) + d882 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1077, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8813 p hg
    simpa only [d1077, d882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1077, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6568 p hg
    simpa only [d1077, d882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8815 (p : Pattern) (guard : d4670 p = 1) : d1078 p ≤ (0 : Int) + d883 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1078, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8805 p hg
    simpa only [d1078, d883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1078, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8814 p hg
    simpa only [d1078, d883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8816 (p : Pattern) (guard : d0 p = 1) : d1080 p ≤ (0 : Int) + d403 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8817 (p : Pattern) (guard : d4670 p = 1) : d1081 p ≤ (0 : Int) + d884 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1081, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7961 p hg
    simpa only [d4670, d1081, d884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1081, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8816 p hg
    simpa only [d4670, d1081, d884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8818 (p : Pattern) (guard : d4395 p = 1) : d1082 p ≤ (0 : Int) + d857 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1082, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3757 p hg
    simpa only [d4395, d1082, d857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1082, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8792 p hg
    simpa only [d4395, d1082, d857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8819 (p : Pattern) (guard : d4670 p = 1) : d1083 p ≤ (0 : Int) + d858 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1083, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8818 p hg
    simpa only [d4670, d1083, d858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1083, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8777 p hg
    simpa only [d4670, d1083, d858, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
