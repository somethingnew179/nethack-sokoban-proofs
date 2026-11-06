/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons263
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare36960 (p : Pattern) (guard : d8112 p = 1) : d3671 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3671, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36959 p hg
    simpa only [d8112, d3671, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3671, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36756 p hg
    simpa only [d8112, d3671, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36961 (p : Pattern) (guard : d8113 p = 1) : d3672 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3672, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36958 p hg
    simpa only [d8113, d3672, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3672, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36960 p hg
    simpa only [d8113, d3672, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36962 (p : Pattern) (guard : d8119 p = 1) : d3677 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3677, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36961 p hg
    simpa only [d8119, d3677, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3677, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36760 p hg
    simpa only [d8119, d3677, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36963 (p : Pattern) (guard : d8125 p = 1) : d3684 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3684, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36962 p hg
    simpa only [d8125, d3684, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3684, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36769 p hg
    simpa only [d8125, d3684, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36964 (p : Pattern) (guard : d8084 p = 1) : d13 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1519 p hg
    simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34338 p hg
    simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36965 (p : Pattern) (guard : d8089 p = 1) : d13 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36964 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36338 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36966 (p : Pattern) (guard : d8094 p = 1) : d13 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36965 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36682 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36967 (p : Pattern) (guard : d8100 p = 1) : d3582 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3582, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36966 p hg
    simpa only [d8100, d3582, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3582, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36685 p hg
    simpa only [d8100, d3582, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36968 (p : Pattern) (guard : d8106 p = 1) : d3665 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3665, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36967 p hg
    simpa only [d8106, d3665, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3665, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36750 p hg
    simpa only [d8106, d3665, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36969 (p : Pattern) (guard : d8112 p = 1) : d3685 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3685, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36968 p hg
    simpa only [d8112, d3685, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3685, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36777 p hg
    simpa only [d8112, d3685, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36970 (p : Pattern) (guard : d8118 p = 1) : d3687 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3687, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36969 p hg
    simpa only [d8118, d3687, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3687, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36780 p hg
    simpa only [d8118, d3687, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36971 (p : Pattern) (guard : d8124 p = 1) : d3690 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3690, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36970 p hg
    simpa only [d8124, d3690, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3690, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36785 p hg
    simpa only [d8124, d3690, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36972 (p : Pattern) (guard : d8130 p = 1) : d3694 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3694, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36971 p hg
    simpa only [d8130, d3694, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3694, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36789 p hg
    simpa only [d8130, d3694, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36973 (p : Pattern) (guard : d8131 p = 1) : d3695 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3695, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36963 p hg
    simpa only [d8131, d3695, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3695, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36972 p hg
    simpa only [d8131, d3695, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36974 (p : Pattern) (guard : d8137 p = 1) : d3716 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d3716, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36973 p hg
    simpa only [d8137, d3716, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d3716, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d3716, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36975 (p : Pattern) (guard : d8138 p = 1) : d3717 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d3717, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36955 p hg
    simpa only [d8138, d3717, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d3717, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36974 p hg
    simpa only [d8138, d3717, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36976 (p : Pattern) (guard : d8139 p = 1) : d3718 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d3718, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36918 p hg
    simpa only [d8139, d3718, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d3718, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36975 p hg
    simpa only [d8139, d3718, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36977 (p : Pattern) (guard : d1 p = 1) : d428 p ≤ (0 : Int) + d428 p := by
  omega
theorem compare36978 (p : Pattern) (guard : d1 p = 1) : d3733 p ≤ (0 : Int) + d429 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3733, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36977 p hg
    simpa only [d3733, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3733, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35085 p hg
    simpa only [d3733, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36979 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35085 p hg
    simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1562 p hg
    simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36980 (p : Pattern) (guard : d1 p = 1) : d3734 p ≤ (0 : Int) + d430 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3734, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36978 p hg
    simpa only [d3734, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3734, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36979 p hg
    simpa only [d3734, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36981 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (0 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35090 p hg
    simpa only [d102, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d102, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36982 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36981 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1562 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36983 (p : Pattern) (guard : d8084 p = 1) : d102 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1562 p hg
    simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35093 p hg
    simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36984 (p : Pattern) (guard : d8085 p = 1) : d102 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36982 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36983 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36985 (p : Pattern) (guard : d8086 p = 1) : d3735 p ≤ (0 : Int) + d431 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d3735, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36980 p hg
    simpa only [d8086, d3735, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d3735, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36984 p hg
    simpa only [d8086, d3735, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36986 (p : Pattern) (guard : d8084 p = 1) : d3736 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1562 p hg
    simpa only [d8084, d3736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35130 p hg
    simpa only [d8084, d3736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36987 (p : Pattern) (guard : d8085 p = 1) : d3737 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3737, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36979 p hg
    simpa only [d8085, d3737, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3737, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36986 p hg
    simpa only [d8085, d3737, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36988 (p : Pattern) (guard : d5847 p = 1) : d3736 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35093 p hg
    simpa only [d5847, d3736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5847, d3736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36989 (p : Pattern) (guard : d8089 p = 1) : d3736 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36986 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36988 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36990 (p : Pattern) (guard : d8090 p = 1) : d3738 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3738, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36987 p hg
    simpa only [d8090, d3738, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3738, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36989 p hg
    simpa only [d8090, d3738, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36991 (p : Pattern) (guard : d8091 p = 1) : d3739 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3739, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36985 p hg
    simpa only [d8091, d3739, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3739, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36990 p hg
    simpa only [d8091, d3739, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36992 (p : Pattern) (guard : d8084 p = 1) : d3740 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1562 p hg
    simpa only [d8084, d3740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35165 p hg
    simpa only [d8084, d3740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36993 (p : Pattern) (guard : d8085 p = 1) : d3741 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3741, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36982 p hg
    simpa only [d8085, d3741, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3741, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36992 p hg
    simpa only [d8085, d3741, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36994 (p : Pattern) (guard : d5847 p = 1) : d3740 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35093 p hg
    simpa only [d5847, d3740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5847, d3740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36995 (p : Pattern) (guard : d8089 p = 1) : d3740 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36992 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36994 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36996 (p : Pattern) (guard : d8090 p = 1) : d3742 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3742, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36993 p hg
    simpa only [d8090, d3742, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3742, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36995 p hg
    simpa only [d8090, d3742, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36997 (p : Pattern) (guard : d8095 p = 1) : d3743 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3743, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36996 p hg
    simpa only [d8095, d3743, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3743, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3743, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36998 (p : Pattern) (guard : d8096 p = 1) : d3744 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3744, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36991 p hg
    simpa only [d8096, d3744, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3744, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36997 p hg
    simpa only [d8096, d3744, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36999 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (0 : Int) + d17 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35106 p hg
    simpa only [d102, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d102, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37000 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (0 : Int) + d339 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36999 p hg
    simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1562 p hg
    simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37001 (p : Pattern) (guard : d8085 p = 1) : d102 p ≤ (0 : Int) + d340 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37000 p hg
    simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36983 p hg
    simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37002 (p : Pattern) (guard : d8084 p = 1) : d102 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4579 p hg
    simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35093 p hg
    simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37003 (p : Pattern) (guard : d5847 p = 1) : d102 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35093 p hg
    simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37004 (p : Pattern) (guard : d8089 p = 1) : d102 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37002 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37003 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37005 (p : Pattern) (guard : d8090 p = 1) : d102 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37001 p hg
    simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37004 p hg
    simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37006 (p : Pattern) (guard : d8089 p = 1) : d3737 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36983 p hg
    simpa only [d8089, d3737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36988 p hg
    simpa only [d8089, d3737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37007 (p : Pattern) (guard : d5854 p = 1) : d3736 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36988 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29469 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37008 (p : Pattern) (guard : d8094 p = 1) : d3738 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37006 p hg
    simpa only [d8094, d3738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37007 p hg
    simpa only [d8094, d3738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37009 (p : Pattern) (guard : d8095 p = 1) : d3745 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3745, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37005 p hg
    simpa only [d8095, d3745, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3745, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37008 p hg
    simpa only [d8095, d3745, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37010 (p : Pattern) (guard : d8089 p = 1) : d3741 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3741, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37002 p hg
    simpa only [d8089, d3741, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3741, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36994 p hg
    simpa only [d8089, d3741, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37011 (p : Pattern) (guard : d5854 p = 1) : d3740 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36994 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29476 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37012 (p : Pattern) (guard : d8094 p = 1) : d3742 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3742, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37010 p hg
    simpa only [d8094, d3742, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3742, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37011 p hg
    simpa only [d8094, d3742, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37013 (p : Pattern) (guard : d8100 p = 1) : d3743 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3743, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37012 p hg
    simpa only [d8100, d3743, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3743, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3743, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37014 (p : Pattern) (guard : d8101 p = 1) : d3746 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3746, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37009 p hg
    simpa only [d8101, d3746, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3746, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37013 p hg
    simpa only [d8101, d3746, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37015 (p : Pattern) (guard : d8102 p = 1) : d3747 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3747, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36998 p hg
    simpa only [d8102, d3747, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3747, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37014 p hg
    simpa only [d8102, d3747, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37016 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (0 : Int) + d348 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1254 p hg
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1562 p hg
    simpa only [d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37017 (p : Pattern) (guard : d8085 p = 1) : d102 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37016 p hg
    simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36983 p hg
    simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37018 (p : Pattern) (guard : d8089 p = 1) : d102 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36983 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37003 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37019 (p : Pattern) (guard : d8090 p = 1) : d102 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37017 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37018 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37020 (p : Pattern) (guard : d8095 p = 1) : d3745 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3745, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37019 p hg
    simpa only [d8095, d3745, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3745, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37008 p hg
    simpa only [d8095, d3745, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37021 (p : Pattern) (guard : d8089 p = 1) : d3741 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36983 p hg
    simpa only [d8089, d3741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36994 p hg
    simpa only [d8089, d3741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37022 (p : Pattern) (guard : d8094 p = 1) : d3742 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37021 p hg
    simpa only [d8094, d3742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37011 p hg
    simpa only [d8094, d3742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37023 (p : Pattern) (guard : d8100 p = 1) : d3743 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37022 p hg
    simpa only [d8100, d3743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37024 (p : Pattern) (guard : d8101 p = 1) : d3746 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3746, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37020 p hg
    simpa only [d8101, d3746, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3746, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37023 p hg
    simpa only [d8101, d3746, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37025 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (0 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35128 p hg
    simpa only [d106, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d106, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37026 (p : Pattern) (guard : d8084 p = 1) : d106 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37025 p hg
    simpa only [d8084, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35130 p hg
    simpa only [d8084, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37027 (p : Pattern) (guard : d5847 p = 1) : d106 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35130 p hg
    simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37028 (p : Pattern) (guard : d8089 p = 1) : d106 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37026 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37027 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37029 (p : Pattern) (guard : d5854 p = 1) : d106 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37027 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37030 (p : Pattern) (guard : d8094 p = 1) : d106 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37028 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37029 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37031 (p : Pattern) (guard : d5854 p = 1) : d3749 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37027 p hg
    simpa only [d5854, d3749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29489 p hg
    simpa only [d5854, d3749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37032 (p : Pattern) (guard : d8099 p = 1) : d3750 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37031 p hg
    simpa only [d8099, d3750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29489 p hg
    simpa only [d8099, d3750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37033 (p : Pattern) (guard : d8100 p = 1) : d3751 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3751, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37030 p hg
    simpa only [d8100, d3751, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3751, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37032 p hg
    simpa only [d8100, d3751, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37034 (p : Pattern) (guard : d5854 p = 1) : d3753 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37027 p hg
    simpa only [d5854, d3753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29496 p hg
    simpa only [d5854, d3753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37035 (p : Pattern) (guard : d8099 p = 1) : d3754 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37034 p hg
    simpa only [d8099, d3754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29496 p hg
    simpa only [d8099, d3754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37036 (p : Pattern) (guard : d8105 p = 1) : d3755 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37035 p hg
    simpa only [d8105, d3755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37037 (p : Pattern) (guard : d8106 p = 1) : d3756 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3756, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37033 p hg
    simpa only [d8106, d3756, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3756, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37036 p hg
    simpa only [d8106, d3756, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37038 (p : Pattern) (guard : d8107 p = 1) : d3757 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3757, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37024 p hg
    simpa only [d8107, d3757, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3757, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37037 p hg
    simpa only [d8107, d3757, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37039 (p : Pattern) (guard : d8108 p = 1) : d3758 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3758, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37015 p hg
    simpa only [d8108, d3758, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3758, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37038 p hg
    simpa only [d8108, d3758, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37040 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (0 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35143 p hg
    simpa only [d102, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d102, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37041 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37040 p hg
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1562 p hg
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37042 (p : Pattern) (guard : d8085 p = 1) : d102 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37041 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36983 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37043 (p : Pattern) (guard : d8090 p = 1) : d102 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37042 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37018 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37044 (p : Pattern) (guard : d8095 p = 1) : d3745 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3745, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37043 p hg
    simpa only [d8095, d3745, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3745, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37008 p hg
    simpa only [d8095, d3745, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37045 (p : Pattern) (guard : d8101 p = 1) : d3746 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3746, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37044 p hg
    simpa only [d8101, d3746, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3746, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37023 p hg
    simpa only [d8101, d3746, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37046 (p : Pattern) (guard : d8084 p = 1) : d106 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1422 p hg
    simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35130 p hg
    simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37047 (p : Pattern) (guard : d8089 p = 1) : d106 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37046 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37027 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37048 (p : Pattern) (guard : d8094 p = 1) : d106 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37047 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37029 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37049 (p : Pattern) (guard : d8100 p = 1) : d3751 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3751, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37048 p hg
    simpa only [d8100, d3751, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3751, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37032 p hg
    simpa only [d8100, d3751, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37050 (p : Pattern) (guard : d8106 p = 1) : d3756 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3756, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37049 p hg
    simpa only [d8106, d3756, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3756, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37036 p hg
    simpa only [d8106, d3756, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37051 (p : Pattern) (guard : d8107 p = 1) : d3757 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3757, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37045 p hg
    simpa only [d8107, d3757, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3757, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37050 p hg
    simpa only [d8107, d3757, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37052 (p : Pattern) (guard : d8112 p = 1) : d3759 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3759, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36863 p hg
    simpa only [d8112, d3759, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3759, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d3759, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37053 (p : Pattern) (guard : d8113 p = 1) : d3760 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3760, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37051 p hg
    simpa only [d8113, d3760, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3760, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37052 p hg
    simpa only [d8113, d3760, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37054 (p : Pattern) (guard : d8114 p = 1) : d3761 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3761, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37039 p hg
    simpa only [d8114, d3761, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3761, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37053 p hg
    simpa only [d8114, d3761, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37055 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1404 p hg
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1562 p hg
    simpa only [d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37056 (p : Pattern) (guard : d8085 p = 1) : d102 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37055 p hg
    simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36983 p hg
    simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37057 (p : Pattern) (guard : d8090 p = 1) : d102 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37056 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37018 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37058 (p : Pattern) (guard : d5847 p = 1) : d3762 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35093 p hg
    simpa only [d5847, d3762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17810 p hg
    simpa only [d5847, d3762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37059 (p : Pattern) (guard : d8089 p = 1) : d3763 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36983 p hg
    simpa only [d8089, d3763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37058 p hg
    simpa only [d8089, d3763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37060 (p : Pattern) (guard : d5854 p = 1) : d3764 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36988 p hg
    simpa only [d5854, d3764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17401 p hg
    simpa only [d5854, d3764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37061 (p : Pattern) (guard : d8094 p = 1) : d3765 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37059 p hg
    simpa only [d8094, d3765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37060 p hg
    simpa only [d8094, d3765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37062 (p : Pattern) (guard : d8095 p = 1) : d3766 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3766, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37057 p hg
    simpa only [d8095, d3766, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3766, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37061 p hg
    simpa only [d8095, d3766, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37063 (p : Pattern) (guard : d8084 p = 1) : d115 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1572 p hg
    simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35165 p hg
    simpa only [d8084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37064 (p : Pattern) (guard : d5847 p = 1) : d3767 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35165 p hg
    simpa only [d5847, d3767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d5847, d3767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37065 (p : Pattern) (guard : d8089 p = 1) : d3768 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37063 p hg
    simpa only [d8089, d3768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37064 p hg
    simpa only [d8089, d3768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37066 (p : Pattern) (guard : d5847 p = 1) : d3769 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35165 p hg
    simpa only [d5847, d3769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17810 p hg
    simpa only [d5847, d3769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37067 (p : Pattern) (guard : d5854 p = 1) : d3770 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37066 p hg
    simpa only [d5854, d3770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17337 p hg
    simpa only [d5854, d3770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37068 (p : Pattern) (guard : d8094 p = 1) : d3771 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37065 p hg
    simpa only [d8094, d3771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37067 p hg
    simpa only [d8094, d3771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37069 (p : Pattern) (guard : d8100 p = 1) : d3772 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37068 p hg
    simpa only [d8100, d3772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37070 (p : Pattern) (guard : d8101 p = 1) : d3773 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3773, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37062 p hg
    simpa only [d8101, d3773, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3773, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37069 p hg
    simpa only [d8101, d3773, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37071 (p : Pattern) (guard : d8084 p = 1) : d102 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1584 p hg
    simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35093 p hg
    simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37072 (p : Pattern) (guard : d8089 p = 1) : d102 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37071 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37003 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37073 (p : Pattern) (guard : d5854 p = 1) : d102 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37003 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37074 (p : Pattern) (guard : d8094 p = 1) : d102 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37072 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37073 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37075 (p : Pattern) (guard : d5854 p = 1) : d3763 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37003 p hg
    simpa only [d5854, d3763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29509 p hg
    simpa only [d5854, d3763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37076 (p : Pattern) (guard : d8099 p = 1) : d3765 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37075 p hg
    simpa only [d8099, d3765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31791 p hg
    simpa only [d8099, d3765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37077 (p : Pattern) (guard : d8100 p = 1) : d3766 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3766, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37074 p hg
    simpa only [d8100, d3766, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3766, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37076 p hg
    simpa only [d8100, d3766, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37078 (p : Pattern) (guard : d5843 p = 1) : d119 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1280 p hg
    simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37079 (p : Pattern) (guard : d5847 p = 1) : d119 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37078 p hg
    simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17810 p hg
    simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37080 (p : Pattern) (guard : d5854 p = 1) : d3774 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37079 p hg
    simpa only [d5854, d3774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17342 p hg
    simpa only [d5854, d3774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37081 (p : Pattern) (guard : d8099 p = 1) : d3777 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37080 p hg
    simpa only [d8099, d3777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31803 p hg
    simpa only [d8099, d3777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37082 (p : Pattern) (guard : d8105 p = 1) : d3778 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37081 p hg
    simpa only [d8105, d3778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37083 (p : Pattern) (guard : d8106 p = 1) : d3779 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3779, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37077 p hg
    simpa only [d8106, d3779, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3779, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37082 p hg
    simpa only [d8106, d3779, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37084 (p : Pattern) (guard : d8107 p = 1) : d3780 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3780, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37070 p hg
    simpa only [d8107, d3780, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3780, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37083 p hg
    simpa only [d8107, d3780, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37085 (p : Pattern) (guard : d8094 p = 1) : d102 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37004 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37073 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37086 (p : Pattern) (guard : d8100 p = 1) : d3766 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3766, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37085 p hg
    simpa only [d8100, d3766, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3766, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37076 p hg
    simpa only [d8100, d3766, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37087 (p : Pattern) (guard : d8106 p = 1) : d3781 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3781, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37086 p hg
    simpa only [d8106, d3781, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3781, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d3781, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37088 (p : Pattern) (guard : d8099 p = 1) : d106 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37029 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37089 (p : Pattern) (guard : d0 p = 1) : d3785 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare37090 (p : Pattern) (guard : d8105 p = 1) : d3786 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37088 p hg
    simpa only [d8105, d3786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37089 p hg
    simpa only [d8105, d3786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37091 (p : Pattern) (guard : d8111 p = 1) : d3787 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37090 p hg
    simpa only [d8111, d3787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37092 (p : Pattern) (guard : d8112 p = 1) : d3788 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3788, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37087 p hg
    simpa only [d8112, d3788, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3788, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37091 p hg
    simpa only [d8112, d3788, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37093 (p : Pattern) (guard : d8113 p = 1) : d3789 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3789, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37084 p hg
    simpa only [d8113, d3789, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3789, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37092 p hg
    simpa only [d8113, d3789, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37094 (p : Pattern) (guard : d8094 p = 1) : d102 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37018 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37073 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37095 (p : Pattern) (guard : d8100 p = 1) : d3766 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37094 p hg
    simpa only [d8100, d3766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37076 p hg
    simpa only [d8100, d3766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37096 (p : Pattern) (guard : d8106 p = 1) : d3781 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37095 p hg
    simpa only [d8106, d3781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d3781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37097 (p : Pattern) (guard : d8112 p = 1) : d3788 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37096 p hg
    simpa only [d8112, d3788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37091 p hg
    simpa only [d8112, d3788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37098 (p : Pattern) (guard : d8117 p = 1) : d3790 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36413 p hg
    simpa only [d8117, d3790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d3790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37099 (p : Pattern) (guard : d8118 p = 1) : d3791 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37097 p hg
    simpa only [d8118, d3791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37098 p hg
    simpa only [d8118, d3791, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
