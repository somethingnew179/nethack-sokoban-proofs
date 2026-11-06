/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons049
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare7000 (p : Pattern) (guard : d4299 p = 1) : d838 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d838, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3199 p hg
    simpa only [d4299, d838, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d838, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6999 p hg
    simpa only [d4299, d838, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7001 (p : Pattern) (guard : d0 p = 1) : d826 p ≤ (0 : Int) + d398 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7002 (p : Pattern) (guard : d4301 p = 1) : d839 p ≤ (0 : Int) + d732 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d839, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7000 p hg
    simpa only [d4301, d839, d732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d839, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7001 p hg
    simpa only [d4301, d839, d732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7003 (p : Pattern) (guard : d0 p = 1) : d390 p ≤ (0 : Int) + d64 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7004 (p : Pattern) (guard : d4299 p = 1) : d840 p ≤ (0 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d840, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3204 p hg
    simpa only [d4299, d840, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d840, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7003 p hg
    simpa only [d4299, d840, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7005 (p : Pattern) (guard : d0 p = 1) : d800 p ≤ (0 : Int) + d409 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7006 (p : Pattern) (guard : d4301 p = 1) : d841 p ≤ (0 : Int) + d733 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d841, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7004 p hg
    simpa only [d4301, d841, d733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d841, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7005 p hg
    simpa only [d4301, d841, d733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7007 (p : Pattern) (guard : d4301 p = 1) : d842 p ≤ (0 : Int) + d734 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d842, d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7002 p hg
    simpa only [d842, d734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d842, d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7006 p hg
    simpa only [d842, d734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7008 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (0 : Int) + d28 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7009 (p : Pattern) (guard : d4299 p = 1) : d843 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d843, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3199 p hg
    simpa only [d4299, d843, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d843, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7008 p hg
    simpa only [d4299, d843, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7010 (p : Pattern) (guard : d4301 p = 1) : d844 p ≤ (0 : Int) + d726 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d844, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7009 p hg
    simpa only [d4301, d844, d726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d844, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6992 p hg
    simpa only [d4301, d844, d726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7011 (p : Pattern) (guard : d4301 p = 1) : d845 p ≤ (0 : Int) + d727 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d845, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7010 p hg
    simpa only [d845, d727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d845, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6965 p hg
    simpa only [d845, d727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7012 (p : Pattern) (guard : d4301 p = 1) : d846 p ≤ (0 : Int) + d735 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d846, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7007 p hg
    simpa only [d846, d735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d846, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7011 p hg
    simpa only [d846, d735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7013 (p : Pattern) (guard : d4301 p = 1) : d847 p ≤ (0 : Int) + d736 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d847, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6966 p hg
    simpa only [d847, d736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d847, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6978 p hg
    simpa only [d847, d736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7014 (p : Pattern) (guard : d4301 p = 1) : d848 p ≤ (0 : Int) + d737 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d848, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7012 p hg
    simpa only [d848, d737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d848, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7013 p hg
    simpa only [d848, d737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7015 (p : Pattern) (guard : d0 p = 1) : d826 p ≤ (0 : Int) + d405 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7016 (p : Pattern) (guard : d4301 p = 1) : d849 p ≤ (0 : Int) + d717 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d849, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6969 p hg
    simpa only [d4301, d849, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d849, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7015 p hg
    simpa only [d4301, d849, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7017 (p : Pattern) (guard : d0 p = 1) : d800 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7018 (p : Pattern) (guard : d4301 p = 1) : d850 p ≤ (0 : Int) + d714 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d850, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6973 p hg
    simpa only [d4301, d850, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d850, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7017 p hg
    simpa only [d4301, d850, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7019 (p : Pattern) (guard : d4301 p = 1) : d851 p ≤ (0 : Int) + d718 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d851, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7016 p hg
    simpa only [d851, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d851, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7018 p hg
    simpa only [d851, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7020 (p : Pattern) (guard : d4301 p = 1) : d852 p ≤ (0 : Int) + d738 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d852, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7019 p hg
    simpa only [d852, d738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d852, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6994 p hg
    simpa only [d852, d738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7021 (p : Pattern) (guard : d4301 p = 1) : d853 p ≤ (0 : Int) + d739 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d853, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7020 p hg
    simpa only [d853, d739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d853, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6996 p hg
    simpa only [d853, d739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7022 (p : Pattern) (guard : d4301 p = 1) : d854 p ≤ (0 : Int) + d740 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d854, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7014 p hg
    simpa only [d854, d740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d854, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7021 p hg
    simpa only [d854, d740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7023 (p : Pattern) (guard : d4301 p = 1) : d855 p ≤ (0 : Int) + d741 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d855, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6998 p hg
    simpa only [d855, d741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d855, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7022 p hg
    simpa only [d855, d741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7024 (p : Pattern) (guard : d0 p = 1) : d372 p ≤ (0 : Int) + d113 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7025 (p : Pattern) (guard : d4299 p = 1) : d856 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d856, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3268 p hg
    simpa only [d4299, d856, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d856, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7024 p hg
    simpa only [d4299, d856, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7026 (p : Pattern) (guard : d0 p = 1) : d858 p ≤ (0 : Int) + d398 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7027 (p : Pattern) (guard : d4301 p = 1) : d859 p ≤ (0 : Int) + d742 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d859, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7025 p hg
    simpa only [d4301, d859, d742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d859, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7026 p hg
    simpa only [d4301, d859, d742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7028 (p : Pattern) (guard : d0 p = 1) : d390 p ≤ (0 : Int) + d137 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7029 (p : Pattern) (guard : d4299 p = 1) : d860 p ≤ (0 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d860, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3273 p hg
    simpa only [d4299, d860, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d860, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7028 p hg
    simpa only [d4299, d860, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7030 (p : Pattern) (guard : d0 p = 1) : d865 p ≤ (0 : Int) + d409 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7031 (p : Pattern) (guard : d4301 p = 1) : d866 p ≤ (0 : Int) + d743 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d866, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7029 p hg
    simpa only [d4301, d866, d743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d866, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7030 p hg
    simpa only [d4301, d866, d743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7032 (p : Pattern) (guard : d4301 p = 1) : d867 p ≤ (0 : Int) + d744 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d867, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7027 p hg
    simpa only [d867, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d867, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7031 p hg
    simpa only [d867, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7033 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (0 : Int) + d113 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7034 (p : Pattern) (guard : d4299 p = 1) : d868 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d868, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3268 p hg
    simpa only [d4299, d868, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d868, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7033 p hg
    simpa only [d4299, d868, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7035 (p : Pattern) (guard : d0 p = 1) : d870 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7036 (p : Pattern) (guard : d4301 p = 1) : d871 p ≤ (0 : Int) + d745 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d871, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7034 p hg
    simpa only [d4301, d871, d745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d871, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7035 p hg
    simpa only [d4301, d871, d745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7037 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d137 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7038 (p : Pattern) (guard : d4299 p = 1) : d872 p ≤ (0 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d872, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3273 p hg
    simpa only [d4299, d872, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d872, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7037 p hg
    simpa only [d4299, d872, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7039 (p : Pattern) (guard : d0 p = 1) : d875 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7040 (p : Pattern) (guard : d4301 p = 1) : d876 p ≤ (0 : Int) + d746 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d876, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7038 p hg
    simpa only [d4301, d876, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d876, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7039 p hg
    simpa only [d4301, d876, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7041 (p : Pattern) (guard : d4301 p = 1) : d877 p ≤ (0 : Int) + d747 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d877, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7036 p hg
    simpa only [d877, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d877, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7040 p hg
    simpa only [d877, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7042 (p : Pattern) (guard : d4301 p = 1) : d878 p ≤ (0 : Int) + d748 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d878, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7032 p hg
    simpa only [d878, d748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d878, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7041 p hg
    simpa only [d878, d748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7043 (p : Pattern) (guard : d0 p = 1) : d394 p ≤ (0 : Int) + d113 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7044 (p : Pattern) (guard : d4299 p = 1) : d879 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d879, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3268 p hg
    simpa only [d4299, d879, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d879, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7043 p hg
    simpa only [d4299, d879, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7045 (p : Pattern) (guard : d0 p = 1) : d870 p ≤ (0 : Int) + d396 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7046 (p : Pattern) (guard : d4301 p = 1) : d880 p ≤ (0 : Int) + d749 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d880, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7044 p hg
    simpa only [d4301, d880, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d880, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7045 p hg
    simpa only [d4301, d880, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7047 (p : Pattern) (guard : d4301 p = 1) : d881 p ≤ (0 : Int) + d750 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d881, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7046 p hg
    simpa only [d881, d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d881, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7040 p hg
    simpa only [d881, d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7048 (p : Pattern) (guard : d4301 p = 1) : d882 p ≤ (0 : Int) + d751 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d882, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7047 p hg
    simpa only [d882, d751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d882, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5952 p hg
    simpa only [d882, d751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7049 (p : Pattern) (guard : d4301 p = 1) : d883 p ≤ (0 : Int) + d752 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d883, d752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7042 p hg
    simpa only [d883, d752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d883, d752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7048 p hg
    simpa only [d883, d752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7050 (p : Pattern) (guard : d0 p = 1) : d403 p ≤ (0 : Int) + d113 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7051 (p : Pattern) (guard : d4299 p = 1) : d884 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d884, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3268 p hg
    simpa only [d4299, d884, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d884, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7050 p hg
    simpa only [d4299, d884, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7052 (p : Pattern) (guard : d0 p = 1) : d858 p ≤ (0 : Int) + d405 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7053 (p : Pattern) (guard : d4301 p = 1) : d885 p ≤ (0 : Int) + d753 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d885, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7051 p hg
    simpa only [d4301, d885, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d885, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7052 p hg
    simpa only [d4301, d885, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7054 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (0 : Int) + d137 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7055 (p : Pattern) (guard : d4299 p = 1) : d886 p ≤ (0 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d886, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3273 p hg
    simpa only [d4299, d886, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d886, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7054 p hg
    simpa only [d4299, d886, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7056 (p : Pattern) (guard : d0 p = 1) : d865 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7057 (p : Pattern) (guard : d4301 p = 1) : d887 p ≤ (0 : Int) + d746 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d887, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7055 p hg
    simpa only [d4301, d887, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d887, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7056 p hg
    simpa only [d4301, d887, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7058 (p : Pattern) (guard : d4301 p = 1) : d888 p ≤ (0 : Int) + d754 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d888, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7053 p hg
    simpa only [d888, d754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d888, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7057 p hg
    simpa only [d888, d754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7059 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d113 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7060 (p : Pattern) (guard : d4299 p = 1) : d889 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d889, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3268 p hg
    simpa only [d4299, d889, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d889, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7059 p hg
    simpa only [d4299, d889, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7061 (p : Pattern) (guard : d4301 p = 1) : d890 p ≤ (0 : Int) + d745 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d890, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7060 p hg
    simpa only [d4301, d890, d745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d890, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7035 p hg
    simpa only [d4301, d890, d745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7062 (p : Pattern) (guard : d4301 p = 1) : d891 p ≤ (0 : Int) + d747 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d891, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7061 p hg
    simpa only [d891, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d891, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7040 p hg
    simpa only [d891, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7063 (p : Pattern) (guard : d4301 p = 1) : d892 p ≤ (0 : Int) + d755 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d892, d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7058 p hg
    simpa only [d892, d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d892, d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7062 p hg
    simpa only [d892, d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7064 (p : Pattern) (guard : d4301 p = 1) : d893 p ≤ (0 : Int) + d756 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d893, d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7062 p hg
    simpa only [d893, d756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d893, d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5911 p hg
    simpa only [d893, d756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7065 (p : Pattern) (guard : d4301 p = 1) : d894 p ≤ (0 : Int) + d757 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d894, d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7063 p hg
    simpa only [d894, d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d894, d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7064 p hg
    simpa only [d894, d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7066 (p : Pattern) (guard : d4301 p = 1) : d895 p ≤ (0 : Int) + d758 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d895, d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7049 p hg
    simpa only [d895, d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d895, d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7065 p hg
    simpa only [d895, d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7067 (p : Pattern) (guard : d4301 p = 1) : d896 p ≤ (0 : Int) + d759 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d896, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6998 p hg
    simpa only [d896, d759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d896, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7066 p hg
    simpa only [d896, d759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7068 (p : Pattern) (guard : d4301 p = 1) : d897 p ≤ (0 : Int) + d760 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d897, d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7023 p hg
    simpa only [d897, d760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d897, d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7067 p hg
    simpa only [d897, d760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7069 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d80 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7070 (p : Pattern) (guard : d4299 p = 1) : d898 p ≤ (0 : Int) + d189 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d898, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3312 p hg
    simpa only [d4299, d898, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d898, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7069 p hg
    simpa only [d4299, d898, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7071 (p : Pattern) (guard : d0 p = 1) : d900 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7072 (p : Pattern) (guard : d4301 p = 1) : d901 p ≤ (0 : Int) + d761 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d901, d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7070 p hg
    simpa only [d4301, d901, d761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d901, d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7071 p hg
    simpa only [d4301, d901, d761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7073 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d84 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7074 (p : Pattern) (guard : d4299 p = 1) : d902 p ≤ (0 : Int) + d200 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d902, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3317 p hg
    simpa only [d4299, d902, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d902, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7073 p hg
    simpa only [d4299, d902, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7075 (p : Pattern) (guard : d0 p = 1) : d904 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7076 (p : Pattern) (guard : d4301 p = 1) : d905 p ≤ (0 : Int) + d762 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d905, d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7074 p hg
    simpa only [d4301, d905, d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d905, d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7075 p hg
    simpa only [d4301, d905, d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7077 (p : Pattern) (guard : d4301 p = 1) : d906 p ≤ (0 : Int) + d763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d906, d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7072 p hg
    simpa only [d906, d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d906, d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7076 p hg
    simpa only [d906, d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7078 (p : Pattern) (guard : d4301 p = 1) : d907 p ≤ (0 : Int) + d764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d907, d764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7019 p hg
    simpa only [d907, d764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d907, d764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7077 p hg
    simpa only [d907, d764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7079 (p : Pattern) (guard : d4301 p = 1) : d908 p ≤ (0 : Int) + d765 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d908, d765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7077 p hg
    simpa only [d908, d765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d908, d765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5911 p hg
    simpa only [d908, d765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7080 (p : Pattern) (guard : d4301 p = 1) : d909 p ≤ (0 : Int) + d766 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d909, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7078 p hg
    simpa only [d909, d766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d909, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7079 p hg
    simpa only [d909, d766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7081 (p : Pattern) (guard : d4301 p = 1) : d910 p ≤ (0 : Int) + d767 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d910, d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7014 p hg
    simpa only [d910, d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d910, d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7080 p hg
    simpa only [d910, d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7082 (p : Pattern) (guard : d4301 p = 1) : d911 p ≤ (0 : Int) + d768 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d911, d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6998 p hg
    simpa only [d911, d768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d911, d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7081 p hg
    simpa only [d911, d768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7083 (p : Pattern) (guard : d0 p = 1) : d451 p ≤ (0 : Int) + d213 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7084 (p : Pattern) (guard : d4299 p = 1) : d912 p ≤ (0 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d912, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3327 p hg
    simpa only [d4299, d912, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d912, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7083 p hg
    simpa only [d4299, d912, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7085 (p : Pattern) (guard : d4301 p = 1) : d913 p ≤ (0 : Int) + d769 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d913, d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7084 p hg
    simpa only [d4301, d913, d769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d913, d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7030 p hg
    simpa only [d4301, d913, d769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7086 (p : Pattern) (guard : d4301 p = 1) : d914 p ≤ (0 : Int) + d770 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d914, d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7027 p hg
    simpa only [d914, d770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d914, d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7085 p hg
    simpa only [d914, d770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7087 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d213 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7088 (p : Pattern) (guard : d4299 p = 1) : d915 p ≤ (0 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d915, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3327 p hg
    simpa only [d4299, d915, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d915, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7087 p hg
    simpa only [d4299, d915, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7089 (p : Pattern) (guard : d4301 p = 1) : d916 p ≤ (0 : Int) + d771 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d916, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7088 p hg
    simpa only [d4301, d916, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d916, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7039 p hg
    simpa only [d4301, d916, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7090 (p : Pattern) (guard : d4301 p = 1) : d917 p ≤ (0 : Int) + d772 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d917, d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7036 p hg
    simpa only [d917, d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d917, d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7089 p hg
    simpa only [d917, d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7091 (p : Pattern) (guard : d4301 p = 1) : d918 p ≤ (0 : Int) + d773 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d918, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7086 p hg
    simpa only [d918, d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d918, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7090 p hg
    simpa only [d918, d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7092 (p : Pattern) (guard : d4301 p = 1) : d919 p ≤ (0 : Int) + d774 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d919, d774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7046 p hg
    simpa only [d919, d774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d919, d774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7089 p hg
    simpa only [d919, d774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7093 (p : Pattern) (guard : d4301 p = 1) : d920 p ≤ (0 : Int) + d775 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d920, d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7092 p hg
    simpa only [d920, d775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d920, d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5952 p hg
    simpa only [d920, d775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7094 (p : Pattern) (guard : d4301 p = 1) : d921 p ≤ (0 : Int) + d776 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d921, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7091 p hg
    simpa only [d921, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d921, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7093 p hg
    simpa only [d921, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7095 (p : Pattern) (guard : d0 p = 1) : d923 p ≤ (0 : Int) + d405 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7096 (p : Pattern) (guard : d4301 p = 1) : d924 p ≤ (0 : Int) + d753 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d924, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7051 p hg
    simpa only [d4301, d924, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d924, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7095 p hg
    simpa only [d4301, d924, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7097 (p : Pattern) (guard : d0 p = 1) : d927 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7098 (p : Pattern) (guard : d4301 p = 1) : d928 p ≤ (0 : Int) + d771 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d928, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7088 p hg
    simpa only [d4301, d928, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d928, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7097 p hg
    simpa only [d4301, d928, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7099 (p : Pattern) (guard : d4301 p = 1) : d929 p ≤ (0 : Int) + d777 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d929, d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7096 p hg
    simpa only [d929, d777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d929, d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7098 p hg
    simpa only [d929, d777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7100 (p : Pattern) (guard : d4299 p = 1) : d930 p ≤ (0 : Int) + d243 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d930, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5991 p hg
    simpa only [d4299, d930, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d930, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7037 p hg
    simpa only [d4299, d930, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7101 (p : Pattern) (guard : d0 p = 1) : d931 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7102 (p : Pattern) (guard : d4301 p = 1) : d932 p ≤ (0 : Int) + d778 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d932, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7100 p hg
    simpa only [d4301, d932, d778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d932, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7101 p hg
    simpa only [d4301, d932, d778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7103 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d154 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7104 (p : Pattern) (guard : d4299 p = 1) : d931 p ≤ (0 : Int) + d246 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d931, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3354 p hg
    simpa only [d4299, d931, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d931, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7103 p hg
    simpa only [d4299, d931, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7105 (p : Pattern) (guard : d0 p = 1) : d934 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7106 (p : Pattern) (guard : d4301 p = 1) : d935 p ≤ (0 : Int) + d779 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d935, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7104 p hg
    simpa only [d4301, d935, d779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d935, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7105 p hg
    simpa only [d4301, d935, d779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7107 (p : Pattern) (guard : d4301 p = 1) : d936 p ≤ (0 : Int) + d780 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d936, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7102 p hg
    simpa only [d936, d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d936, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7106 p hg
    simpa only [d936, d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7108 (p : Pattern) (guard : d4301 p = 1) : d937 p ≤ (0 : Int) + d781 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d937, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7099 p hg
    simpa only [d937, d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d937, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7107 p hg
    simpa only [d937, d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7109 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d255 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7110 (p : Pattern) (guard : d4299 p = 1) : d938 p ≤ (0 : Int) + d256 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d938, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3349 p hg
    simpa only [d4299, d938, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d938, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7109 p hg
    simpa only [d4299, d938, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7111 (p : Pattern) (guard : d0 p = 1) : d940 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7112 (p : Pattern) (guard : d4301 p = 1) : d941 p ≤ (0 : Int) + d782 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d941, d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7110 p hg
    simpa only [d4301, d941, d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d941, d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7111 p hg
    simpa only [d4301, d941, d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7113 (p : Pattern) (guard : d4301 p = 1) : d942 p ≤ (0 : Int) + d783 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d942, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7112 p hg
    simpa only [d942, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d942, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7106 p hg
    simpa only [d942, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7114 (p : Pattern) (guard : d4301 p = 1) : d943 p ≤ (0 : Int) + d784 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d943, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7113 p hg
    simpa only [d943, d784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d943, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5911 p hg
    simpa only [d943, d784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7115 (p : Pattern) (guard : d4301 p = 1) : d944 p ≤ (0 : Int) + d785 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d944, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7108 p hg
    simpa only [d944, d785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d944, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7114 p hg
    simpa only [d944, d785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7116 (p : Pattern) (guard : d4301 p = 1) : d945 p ≤ (0 : Int) + d786 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d945, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7094 p hg
    simpa only [d945, d786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d945, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7115 p hg
    simpa only [d945, d786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7117 (p : Pattern) (guard : d4301 p = 1) : d946 p ≤ (0 : Int) + d787 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d946, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6998 p hg
    simpa only [d946, d787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d946, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7116 p hg
    simpa only [d946, d787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7118 (p : Pattern) (guard : d4301 p = 1) : d947 p ≤ (0 : Int) + d788 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d947, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7082 p hg
    simpa only [d947, d788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d947, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7117 p hg
    simpa only [d947, d788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7119 (p : Pattern) (guard : d4301 p = 1) : d948 p ≤ (0 : Int) + d789 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d948, d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7068 p hg
    simpa only [d948, d789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d948, d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7118 p hg
    simpa only [d948, d789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7120 (p : Pattern) (guard : d0 p = 1) : d790 p ≤ (2 : Int) + d29 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7121 (p : Pattern) (guard : d1 p = 1) : d791 p ≤ (2 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d791, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4693 p hg
    simpa only [d791, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d791, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4742 p hg
    simpa only [d791, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7122 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (2 : Int) + d28 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7123 (p : Pattern) (guard : d4299 p = 1) : d792 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d792, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7121 p hg
    simpa only [d4299, d792, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d792, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7122 p hg
    simpa only [d4299, d792, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7124 (p : Pattern) (guard : d4432 p = 1) : d793 p ≤ (2 : Int) + d29 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7120 p hg
    simpa only [d4432, d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7123 p hg
    simpa only [d4432, d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7125 (p : Pattern) (guard : d0 p = 1) : d794 p ≤ (2 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7126 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (2 : Int) + d31 p := by
  omega
theorem compare7127 (p : Pattern) (guard : d1 p = 1) : d795 p ≤ (2 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d795, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7126 p hg
    simpa only [d795, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d795, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4868 p hg
    simpa only [d795, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7128 (p : Pattern) (guard : d1 p = 1) : d796 p ≤ (2 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d796, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4740 p hg
    simpa only [d796, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d796, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7127 p hg
    simpa only [d796, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7129 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (2 : Int) + d18 p := by
  omega
theorem compare7130 (p : Pattern) (guard : d1 p = 1) : d797 p ≤ (2 : Int) + d20 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d797, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7129 p hg
    simpa only [d797, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d797, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4700 p hg
    simpa only [d797, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7131 (p : Pattern) (guard : d1 p = 1) : d798 p ≤ (2 : Int) + d55 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d798, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7130 p hg
    simpa only [d798, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d798, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4743 p hg
    simpa only [d798, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7132 (p : Pattern) (guard : d1 p = 1) : d799 p ≤ (2 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d799, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7128 p hg
    simpa only [d799, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d799, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7131 p hg
    simpa only [d799, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7133 (p : Pattern) (guard : d4299 p = 1) : d800 p ≤ (2 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d800, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7132 p hg
    simpa only [d4299, d800, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d800, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4754 p hg
    simpa only [d4299, d800, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7134 (p : Pattern) (guard : d4432 p = 1) : d801 p ≤ (2 : Int) + d65 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7125 p hg
    simpa only [d4432, d801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7133 p hg
    simpa only [d4432, d801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7135 (p : Pattern) (guard : d4432 p = 1) : d802 p ≤ (2 : Int) + d4729 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d802, d4729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7124 p hg
    simpa only [d802, d4729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d802, d4729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7134 p hg
    simpa only [d802, d4729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7136 (p : Pattern) (guard : d0 p = 1) : d803 p ≤ (2 : Int) + d29 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7137 (p : Pattern) (guard : d1 p = 1) : d804 p ≤ (2 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d804, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4740 p hg
    simpa only [d804, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d804, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4742 p hg
    simpa only [d804, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7138 (p : Pattern) (guard : d4299 p = 1) : d805 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d805, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7137 p hg
    simpa only [d4299, d805, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d805, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4746 p hg
    simpa only [d4299, d805, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7139 (p : Pattern) (guard : d4432 p = 1) : d806 p ≤ (2 : Int) + d29 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7136 p hg
    simpa only [d4432, d806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7138 p hg
    simpa only [d4432, d806, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
