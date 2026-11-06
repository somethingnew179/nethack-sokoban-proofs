/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons034
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare4900 (p : Pattern) (guard : d1176 p = 1) : d535 p ≤ (3 : Int) + d83 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d535, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4881 p hg
    simpa only [d535, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d535, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4899 p hg
    simpa only [d535, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4901 (p : Pattern) (guard : d1176 p = 1) : d536 p ≤ (3 : Int) + d84 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d536, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4900 p hg
    simpa only [d536, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d536, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4884 p hg
    simpa only [d536, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4902 (p : Pattern) (guard : d1176 p = 1) : d537 p ≤ (3 : Int) + d85 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d537, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4898 p hg
    simpa only [d537, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d537, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4901 p hg
    simpa only [d537, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4903 (p : Pattern) (guard : d1176 p = 1) : d538 p ≤ (3 : Int) + d162 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d538, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4898 p hg
    simpa only [d538, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d538, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4902 p hg
    simpa only [d538, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4904 (p : Pattern) (guard : d1176 p = 1) : d539 p ≤ (3 : Int) + d1060 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d539, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4884 p hg
    simpa only [d539, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d539, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d539, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4905 (p : Pattern) (guard : d1176 p = 1) : d540 p ≤ (3 : Int) + d1061 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d540, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4890 p hg
    simpa only [d540, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d540, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4904 p hg
    simpa only [d540, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4906 (p : Pattern) (guard : d1176 p = 1) : d541 p ≤ (3 : Int) + d1062 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d541, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4889 p hg
    simpa only [d541, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d541, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d541, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4907 (p : Pattern) (guard : d1176 p = 1) : d542 p ≤ (3 : Int) + d1063 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d542, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4889 p hg
    simpa only [d542, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d542, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4906 p hg
    simpa only [d542, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4908 (p : Pattern) (guard : d1176 p = 1) : d543 p ≤ (3 : Int) + d1064 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d543, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4900 p hg
    simpa only [d543, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d543, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4907 p hg
    simpa only [d543, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4909 (p : Pattern) (guard : d1176 p = 1) : d544 p ≤ (3 : Int) + d1065 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d544, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4908 p hg
    simpa only [d544, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d544, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4904 p hg
    simpa only [d544, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4910 (p : Pattern) (guard : d1176 p = 1) : d545 p ≤ (3 : Int) + d1066 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d545, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4905 p hg
    simpa only [d545, d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d545, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4909 p hg
    simpa only [d545, d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4911 (p : Pattern) (guard : d1176 p = 1) : d546 p ≤ (3 : Int) + d1067 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d546, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4905 p hg
    simpa only [d546, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d546, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4910 p hg
    simpa only [d546, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4912 (p : Pattern) (guard : d1176 p = 1) : d547 p ≤ (3 : Int) + d1068 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d547, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4903 p hg
    simpa only [d547, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d547, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4911 p hg
    simpa only [d547, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4913 (p : Pattern) (guard : d1176 p = 1) : d548 p ≤ (3 : Int) + d1069 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d548, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4897 p hg
    simpa only [d548, d1069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d548, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4912 p hg
    simpa only [d548, d1069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4914 (p : Pattern) (guard : d1176 p = 1) : d549 p ≤ (3 : Int) + d48 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d549, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4886 p hg
    simpa only [d549, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d549, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4884 p hg
    simpa only [d549, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4915 (p : Pattern) (guard : d1176 p = 1) : d550 p ≤ (3 : Int) + d1070 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d550, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4896 p hg
    simpa only [d550, d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d550, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4904 p hg
    simpa only [d550, d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4916 (p : Pattern) (guard : d1176 p = 1) : d551 p ≤ (3 : Int) + d1071 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d551, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4914 p hg
    simpa only [d551, d1071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d551, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4915 p hg
    simpa only [d551, d1071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4917 (p : Pattern) (guard : d1176 p = 1) : d552 p ≤ (3 : Int) + d164 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d552, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4902 p hg
    simpa only [d552, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d552, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4884 p hg
    simpa only [d552, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4918 (p : Pattern) (guard : d1176 p = 1) : d553 p ≤ (3 : Int) + d1072 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d553, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4910 p hg
    simpa only [d553, d1072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d553, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4904 p hg
    simpa only [d553, d1072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4919 (p : Pattern) (guard : d1176 p = 1) : d554 p ≤ (3 : Int) + d1073 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d554, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4917 p hg
    simpa only [d554, d1073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d554, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4918 p hg
    simpa only [d554, d1073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4920 (p : Pattern) (guard : d1176 p = 1) : d555 p ≤ (3 : Int) + d1074 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d555, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4916 p hg
    simpa only [d555, d1074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d555, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4919 p hg
    simpa only [d555, d1074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4921 (p : Pattern) (guard : d1176 p = 1) : d556 p ≤ (3 : Int) + d1075 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d556, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4913 p hg
    simpa only [d556, d1075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d556, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4920 p hg
    simpa only [d556, d1075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4922 (p : Pattern) (guard : d1176 p = 1) : d557 p ≤ (3 : Int) + d1076 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d557, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4884 p hg
    simpa only [d557, d1076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d557, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4904 p hg
    simpa only [d557, d1076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4923 (p : Pattern) (guard : d1176 p = 1) : d558 p ≤ (3 : Int) + d1077 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d558, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4920 p hg
    simpa only [d558, d1077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d558, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4922 p hg
    simpa only [d558, d1077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4924 (p : Pattern) (guard : d1176 p = 1) : d559 p ≤ (3 : Int) + d1078 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d559, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4921 p hg
    simpa only [d559, d1078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d559, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4923 p hg
    simpa only [d559, d1078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4925 (p : Pattern) (guard : d1176 p = 1) : d560 p ≤ (3 : Int) + d92 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d560, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4899 p hg
    simpa only [d560, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d560, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4884 p hg
    simpa only [d560, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4926 (p : Pattern) (guard : d1176 p = 1) : d561 p ≤ (3 : Int) + d94 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d561, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4900 p hg
    simpa only [d561, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d561, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4925 p hg
    simpa only [d561, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4927 (p : Pattern) (guard : d1176 p = 1) : d562 p ≤ (3 : Int) + d100 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d562, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4886 p hg
    simpa only [d562, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d562, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4926 p hg
    simpa only [d562, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4928 (p : Pattern) (guard : d1176 p = 1) : d563 p ≤ (3 : Int) + d169 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d563, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4886 p hg
    simpa only [d563, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d563, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4927 p hg
    simpa only [d563, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4929 (p : Pattern) (guard : d1176 p = 1) : d564 p ≤ (3 : Int) + d1079 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d564, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4906 p hg
    simpa only [d564, d1079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d564, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d564, d1079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4930 (p : Pattern) (guard : d1176 p = 1) : d565 p ≤ (3 : Int) + d1080 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d565, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4925 p hg
    simpa only [d565, d1080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d565, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4929 p hg
    simpa only [d565, d1080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4931 (p : Pattern) (guard : d1176 p = 1) : d566 p ≤ (3 : Int) + d1081 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d566, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4908 p hg
    simpa only [d566, d1081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d566, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4930 p hg
    simpa only [d566, d1081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4932 (p : Pattern) (guard : d1176 p = 1) : d567 p ≤ (3 : Int) + d1082 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d567, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4896 p hg
    simpa only [d567, d1082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d567, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4931 p hg
    simpa only [d567, d1082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4933 (p : Pattern) (guard : d1176 p = 1) : d568 p ≤ (3 : Int) + d1083 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d568, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4896 p hg
    simpa only [d568, d1083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d568, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4932 p hg
    simpa only [d568, d1083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4934 (p : Pattern) (guard : d1176 p = 1) : d569 p ≤ (3 : Int) + d1084 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d569, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4928 p hg
    simpa only [d569, d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d569, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4933 p hg
    simpa only [d569, d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4935 (p : Pattern) (guard : d1176 p = 1) : d570 p ≤ (3 : Int) + d1085 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d570, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4934 p hg
    simpa only [d570, d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d570, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4922 p hg
    simpa only [d570, d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4936 (p : Pattern) (guard : d1176 p = 1) : d571 p ≤ (3 : Int) + d93 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d571, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4881 p hg
    simpa only [d571, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d571, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4925 p hg
    simpa only [d571, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4937 (p : Pattern) (guard : d1176 p = 1) : d572 p ≤ (3 : Int) + d95 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d572, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4936 p hg
    simpa only [d572, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d572, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4926 p hg
    simpa only [d572, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4938 (p : Pattern) (guard : d1176 p = 1) : d573 p ≤ (3 : Int) + d171 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d573, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4937 p hg
    simpa only [d573, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d573, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4884 p hg
    simpa only [d573, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4939 (p : Pattern) (guard : d1176 p = 1) : d574 p ≤ (3 : Int) + d1086 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d574, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4890 p hg
    simpa only [d574, d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d574, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4930 p hg
    simpa only [d574, d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4940 (p : Pattern) (guard : d1176 p = 1) : d575 p ≤ (3 : Int) + d1087 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d575, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4939 p hg
    simpa only [d575, d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d575, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4931 p hg
    simpa only [d575, d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4941 (p : Pattern) (guard : d1176 p = 1) : d576 p ≤ (3 : Int) + d1088 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d576, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4940 p hg
    simpa only [d576, d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d576, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4904 p hg
    simpa only [d576, d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4942 (p : Pattern) (guard : d1176 p = 1) : d577 p ≤ (3 : Int) + d1089 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d577, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4938 p hg
    simpa only [d577, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d577, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4941 p hg
    simpa only [d577, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4943 (p : Pattern) (guard : d1176 p = 1) : d578 p ≤ (3 : Int) + d1090 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d578, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4942 p hg
    simpa only [d578, d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d578, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4922 p hg
    simpa only [d578, d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4944 (p : Pattern) (guard : d1176 p = 1) : d579 p ≤ (3 : Int) + d1091 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d579, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4935 p hg
    simpa only [d579, d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d579, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4943 p hg
    simpa only [d579, d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4945 (p : Pattern) (guard : d1176 p = 1) : d580 p ≤ (3 : Int) + d174 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d580, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4927 p hg
    simpa only [d580, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d580, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4884 p hg
    simpa only [d580, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4946 (p : Pattern) (guard : d1176 p = 1) : d581 p ≤ (3 : Int) + d1092 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d581, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4932 p hg
    simpa only [d581, d1092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d581, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4904 p hg
    simpa only [d581, d1092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4947 (p : Pattern) (guard : d1176 p = 1) : d582 p ≤ (3 : Int) + d1093 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d582, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4945 p hg
    simpa only [d582, d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d582, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4946 p hg
    simpa only [d582, d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4948 (p : Pattern) (guard : d1176 p = 1) : d583 p ≤ (3 : Int) + d1094 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d583, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4947 p hg
    simpa only [d583, d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d583, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4922 p hg
    simpa only [d583, d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4949 (p : Pattern) (guard : d1176 p = 1) : d584 p ≤ (3 : Int) + d1095 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d584, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4948 p hg
    simpa only [d584, d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d584, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4922 p hg
    simpa only [d584, d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4950 (p : Pattern) (guard : d1176 p = 1) : d585 p ≤ (3 : Int) + d1096 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d585, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4944 p hg
    simpa only [d585, d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d585, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4949 p hg
    simpa only [d585, d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4951 (p : Pattern) (guard : d1176 p = 1) : d586 p ≤ (3 : Int) + d1097 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d586, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4924 p hg
    simpa only [d586, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d586, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4950 p hg
    simpa only [d586, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4952 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4953 (p : Pattern) (guard : d917 p = 1) : d6 p ≤ (0 : Int) + d0 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d917, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4952 p hg
    simpa only [d917, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4954 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4955 (p : Pattern) (guard : d917 p = 1) : d28 p ≤ (0 : Int) + d6 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d28, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d917, d28, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d28, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4954 p hg
    simpa only [d917, d28, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4956 (p : Pattern) (guard : d917 p = 1) : d29 p ≤ (0 : Int) + d7 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d29, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4953 p hg
    simpa only [d29, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d29, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4955 p hg
    simpa only [d29, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4957 (p : Pattern) (guard : d0 p = 1) : d9 p ≤ (0 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4958 (p : Pattern) (guard : d917 p = 1) : d14 p ≤ (0 : Int) + d0 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d917, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4957 p hg
    simpa only [d917, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4959 (p : Pattern) (guard : d917 p = 1) : d30 p ≤ (0 : Int) + d7 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d30, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4958 p hg
    simpa only [d30, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d30, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4955 p hg
    simpa only [d30, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4960 (p : Pattern) (guard : d917 p = 1) : d31 p ≤ (0 : Int) + d7 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4956 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4959 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4961 (p : Pattern) (guard : d0 p = 1) : d4 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4962 (p : Pattern) (guard : d917 p = 1) : d54 p ≤ (0 : Int) + d2 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d917, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4961 p hg
    simpa only [d917, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4963 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (0 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4964 (p : Pattern) (guard : d917 p = 1) : d587 p ≤ (0 : Int) + d54 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d587, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d917, d587, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d587, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4963 p hg
    simpa only [d917, d587, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4965 (p : Pattern) (guard : d917 p = 1) : d588 p ≤ (0 : Int) + d55 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d588, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4962 p hg
    simpa only [d588, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d588, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4964 p hg
    simpa only [d588, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4966 (p : Pattern) (guard : d917 p = 1) : d589 p ≤ (0 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d589, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4956 p hg
    simpa only [d589, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d589, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4965 p hg
    simpa only [d589, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4967 (p : Pattern) (guard : d0 p = 1) : d58 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4968 (p : Pattern) (guard : d917 p = 1) : d259 p ≤ (0 : Int) + d2 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d917, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4967 p hg
    simpa only [d917, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4969 (p : Pattern) (guard : d917 p = 1) : d590 p ≤ (0 : Int) + d55 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d590, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4968 p hg
    simpa only [d590, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d590, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4964 p hg
    simpa only [d590, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4970 (p : Pattern) (guard : d917 p = 1) : d591 p ≤ (0 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d591, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4959 p hg
    simpa only [d591, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d591, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4969 p hg
    simpa only [d591, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4971 (p : Pattern) (guard : d917 p = 1) : d592 p ≤ (0 : Int) + d56 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4966 p hg
    simpa only [d592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4970 p hg
    simpa only [d592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4972 (p : Pattern) (guard : d917 p = 1) : d593 p ≤ (0 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d593, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4960 p hg
    simpa only [d593, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d593, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4971 p hg
    simpa only [d593, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4973 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (0 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4974 (p : Pattern) (guard : d917 p = 1) : d32 p ≤ (0 : Int) + d8 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare908 p hg
    simpa only [d917, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4973 p hg
    simpa only [d917, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4975 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (0 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4976 (p : Pattern) (guard : d917 p = 1) : d32 p ≤ (0 : Int) + d10 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d32, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare908 p hg
    simpa only [d917, d32, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d32, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4975 p hg
    simpa only [d917, d32, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4977 (p : Pattern) (guard : d917 p = 1) : d32 p ≤ (0 : Int) + d11 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4974 p hg
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4976 p hg
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4978 (p : Pattern) (guard : d917 p = 1) : d33 p ≤ (0 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d33, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4959 p hg
    simpa only [d33, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d33, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4977 p hg
    simpa only [d33, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4979 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (0 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4980 (p : Pattern) (guard : d917 p = 1) : d594 p ≤ (0 : Int) + d9 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare913 p hg
    simpa only [d917, d594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4979 p hg
    simpa only [d917, d594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4981 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (0 : Int) + d58 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4982 (p : Pattern) (guard : d917 p = 1) : d594 p ≤ (0 : Int) + d59 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d594, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare913 p hg
    simpa only [d917, d594, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d594, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4981 p hg
    simpa only [d917, d594, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4983 (p : Pattern) (guard : d917 p = 1) : d594 p ≤ (0 : Int) + d60 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4980 p hg
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4982 p hg
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4984 (p : Pattern) (guard : d917 p = 1) : d595 p ≤ (0 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d595, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4977 p hg
    simpa only [d595, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d595, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4983 p hg
    simpa only [d595, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4985 (p : Pattern) (guard : d917 p = 1) : d596 p ≤ (0 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d596, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4970 p hg
    simpa only [d596, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d596, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4984 p hg
    simpa only [d596, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4986 (p : Pattern) (guard : d917 p = 1) : d597 p ≤ (0 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d597, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4978 p hg
    simpa only [d597, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d597, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4985 p hg
    simpa only [d597, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4987 (p : Pattern) (guard : d917 p = 1) : d598 p ≤ (0 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d598, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4972 p hg
    simpa only [d598, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d598, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4986 p hg
    simpa only [d598, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4988 (p : Pattern) (guard : d917 p = 1) : d599 p ≤ (0 : Int) + d55 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4965 p hg
    simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4969 p hg
    simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4989 (p : Pattern) (guard : d917 p = 1) : d600 p ≤ (0 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d600, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4960 p hg
    simpa only [d600, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d600, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4988 p hg
    simpa only [d600, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4990 (p : Pattern) (guard : d917 p = 1) : d601 p ≤ (0 : Int) + d119 p := by
  cases selected : p 187 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d601, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4956 p hg
    simpa only [d601, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d601, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4965 p hg
    simpa only [d601, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4991 (p : Pattern) (guard : d917 p = 1) : d602 p ≤ (0 : Int) + d120 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d602, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4956 p hg
    simpa only [d602, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d602, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4990 p hg
    simpa only [d602, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4992 (p : Pattern) (guard : d917 p = 1) : d603 p ≤ (0 : Int) + d119 p := by
  cases selected : p 187 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d603, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4959 p hg
    simpa only [d603, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d603, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4969 p hg
    simpa only [d603, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4993 (p : Pattern) (guard : d917 p = 1) : d604 p ≤ (0 : Int) + d120 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d604, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4959 p hg
    simpa only [d604, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d604, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4992 p hg
    simpa only [d604, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4994 (p : Pattern) (guard : d917 p = 1) : d605 p ≤ (0 : Int) + d120 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4991 p hg
    simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4993 p hg
    simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4995 (p : Pattern) (guard : d917 p = 1) : d606 p ≤ (0 : Int) + d121 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d606, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4994 p hg
    simpa only [d606, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d606, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4988 p hg
    simpa only [d606, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4996 (p : Pattern) (guard : d917 p = 1) : d607 p ≤ (0 : Int) + d122 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d607, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4989 p hg
    simpa only [d607, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d607, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4995 p hg
    simpa only [d607, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4997 (p : Pattern) (guard : d917 p = 1) : d608 p ≤ (0 : Int) + d179 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d608, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4989 p hg
    simpa only [d608, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d608, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4996 p hg
    simpa only [d608, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4998 (p : Pattern) (guard : d917 p = 1) : d609 p ≤ (0 : Int) + d65 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d609, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4969 p hg
    simpa only [d609, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d609, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4983 p hg
    simpa only [d609, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4999 (p : Pattern) (guard : d917 p = 1) : d610 p ≤ (0 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d610, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4978 p hg
    simpa only [d610, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d610, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4998 p hg
    simpa only [d610, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5000 (p : Pattern) (guard : d917 p = 1) : d611 p ≤ (0 : Int) + d125 p := by
  cases selected : p 187 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d611, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4977 p hg
    simpa only [d611, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d611, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4983 p hg
    simpa only [d611, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5001 (p : Pattern) (guard : d917 p = 1) : d612 p ≤ (0 : Int) + d126 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d612, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4977 p hg
    simpa only [d612, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d612, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5000 p hg
    simpa only [d612, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5002 (p : Pattern) (guard : d917 p = 1) : d613 p ≤ (0 : Int) + d127 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d613, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4993 p hg
    simpa only [d613, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d613, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5001 p hg
    simpa only [d613, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5003 (p : Pattern) (guard : d917 p = 1) : d614 p ≤ (0 : Int) + d128 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d614, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5002 p hg
    simpa only [d614, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d614, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4998 p hg
    simpa only [d614, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5004 (p : Pattern) (guard : d917 p = 1) : d615 p ≤ (0 : Int) + d129 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d615, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4999 p hg
    simpa only [d615, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d615, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5003 p hg
    simpa only [d615, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5005 (p : Pattern) (guard : d917 p = 1) : d616 p ≤ (0 : Int) + d237 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d616, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4999 p hg
    simpa only [d616, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d616, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5004 p hg
    simpa only [d616, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5006 (p : Pattern) (guard : d917 p = 1) : d617 p ≤ (0 : Int) + d238 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d617, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4997 p hg
    simpa only [d617, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d617, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5005 p hg
    simpa only [d617, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5007 (p : Pattern) (guard : d917 p = 1) : d618 p ≤ (0 : Int) + d239 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d618, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4987 p hg
    simpa only [d618, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d618, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5006 p hg
    simpa only [d618, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5008 (p : Pattern) (guard : d917 p = 1) : d619 p ≤ (0 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d619, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4972 p hg
    simpa only [d619, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d619, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4988 p hg
    simpa only [d619, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5009 (p : Pattern) (guard : d917 p = 1) : d620 p ≤ (0 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d620, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4986 p hg
    simpa only [d620, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d620, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4998 p hg
    simpa only [d620, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5010 (p : Pattern) (guard : d917 p = 1) : d621 p ≤ (0 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d621, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5008 p hg
    simpa only [d621, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d621, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5009 p hg
    simpa only [d621, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5011 (p : Pattern) (guard : d917 p = 1) : d622 p ≤ (0 : Int) + d181 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d622, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4996 p hg
    simpa only [d622, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d622, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4988 p hg
    simpa only [d622, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5012 (p : Pattern) (guard : d917 p = 1) : d623 p ≤ (0 : Int) + d240 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d623, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5004 p hg
    simpa only [d623, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d623, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4998 p hg
    simpa only [d623, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5013 (p : Pattern) (guard : d917 p = 1) : d624 p ≤ (0 : Int) + d241 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d624, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5011 p hg
    simpa only [d624, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d624, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5012 p hg
    simpa only [d624, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5014 (p : Pattern) (guard : d917 p = 1) : d625 p ≤ (0 : Int) + d242 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d625, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5010 p hg
    simpa only [d625, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d625, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5013 p hg
    simpa only [d625, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5015 (p : Pattern) (guard : d917 p = 1) : d626 p ≤ (0 : Int) + d243 p := by
  cases selected : p 133 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d626, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5007 p hg
    simpa only [d626, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d626, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5014 p hg
    simpa only [d626, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5016 (p : Pattern) (guard : d917 p = 1) : d627 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d627, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4988 p hg
    simpa only [d627, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d627, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4998 p hg
    simpa only [d627, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5017 (p : Pattern) (guard : d917 p = 1) : d628 p ≤ (0 : Int) + d244 p := by
  cases selected : p 133 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d628, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5014 p hg
    simpa only [d628, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d628, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5016 p hg
    simpa only [d628, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5018 (p : Pattern) (guard : d917 p = 1) : d629 p ≤ (0 : Int) + d245 p := by
  cases selected : p 132 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d629, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5015 p hg
    simpa only [d629, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d629, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5017 p hg
    simpa only [d629, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5019 (p : Pattern) (guard : d917 p = 1) : d630 p ≤ (0 : Int) + d137 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d630, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4990 p hg
    simpa only [d630, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d630, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4965 p hg
    simpa only [d630, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5020 (p : Pattern) (guard : d917 p = 1) : d631 p ≤ (0 : Int) + d137 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d631, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4992 p hg
    simpa only [d631, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d631, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4969 p hg
    simpa only [d631, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5021 (p : Pattern) (guard : d917 p = 1) : d632 p ≤ (0 : Int) + d137 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5019 p hg
    simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5020 p hg
    simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5022 (p : Pattern) (guard : d917 p = 1) : d633 p ≤ (0 : Int) + d139 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d633, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4994 p hg
    simpa only [d633, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d633, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5021 p hg
    simpa only [d633, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5023 (p : Pattern) (guard : d917 p = 1) : d634 p ≤ (0 : Int) + d153 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d634, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4972 p hg
    simpa only [d634, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d634, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5022 p hg
    simpa only [d634, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5024 (p : Pattern) (guard : d917 p = 1) : d635 p ≤ (0 : Int) + d186 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d635, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4972 p hg
    simpa only [d635, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d635, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5023 p hg
    simpa only [d635, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5025 (p : Pattern) (guard : d917 p = 1) : d636 p ≤ (0 : Int) + d143 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d636, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5000 p hg
    simpa only [d636, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d636, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4983 p hg
    simpa only [d636, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5026 (p : Pattern) (guard : d917 p = 1) : d637 p ≤ (0 : Int) + d144 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d637, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5020 p hg
    simpa only [d637, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d637, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5025 p hg
    simpa only [d637, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5027 (p : Pattern) (guard : d917 p = 1) : d638 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d638, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5002 p hg
    simpa only [d638, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d638, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5026 p hg
    simpa only [d638, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5028 (p : Pattern) (guard : d917 p = 1) : d639 p ≤ (0 : Int) + d155 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d639, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4986 p hg
    simpa only [d639, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d639, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5027 p hg
    simpa only [d639, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5029 (p : Pattern) (guard : d917 p = 1) : d640 p ≤ (0 : Int) + d246 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d640, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4986 p hg
    simpa only [d640, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d640, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5028 p hg
    simpa only [d640, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5030 (p : Pattern) (guard : d917 p = 1) : d641 p ≤ (0 : Int) + d247 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d641, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5024 p hg
    simpa only [d641, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d641, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5029 p hg
    simpa only [d641, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5031 (p : Pattern) (guard : d917 p = 1) : d642 p ≤ (0 : Int) + d248 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d642, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5030 p hg
    simpa only [d642, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d642, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5016 p hg
    simpa only [d642, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5032 (p : Pattern) (guard : d917 p = 1) : d643 p ≤ (0 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d643, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4960 p hg
    simpa only [d643, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d643, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5021 p hg
    simpa only [d643, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5033 (p : Pattern) (guard : d917 p = 1) : d644 p ≤ (0 : Int) + d140 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d644, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5032 p hg
    simpa only [d644, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d644, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5022 p hg
    simpa only [d644, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5034 (p : Pattern) (guard : d917 p = 1) : d645 p ≤ (0 : Int) + d188 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d645, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5033 p hg
    simpa only [d645, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d645, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4988 p hg
    simpa only [d645, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5035 (p : Pattern) (guard : d917 p = 1) : d646 p ≤ (0 : Int) + d145 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d646, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4978 p hg
    simpa only [d646, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d646, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5026 p hg
    simpa only [d646, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5036 (p : Pattern) (guard : d917 p = 1) : d647 p ≤ (0 : Int) + d147 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d647, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5035 p hg
    simpa only [d647, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d647, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5027 p hg
    simpa only [d647, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5037 (p : Pattern) (guard : d917 p = 1) : d648 p ≤ (0 : Int) + d249 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d648, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5036 p hg
    simpa only [d648, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d648, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4998 p hg
    simpa only [d648, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5038 (p : Pattern) (guard : d917 p = 1) : d649 p ≤ (0 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d649, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5034 p hg
    simpa only [d649, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d649, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5037 p hg
    simpa only [d649, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5039 (p : Pattern) (guard : d917 p = 1) : d650 p ≤ (0 : Int) + d251 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d650, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5038 p hg
    simpa only [d650, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d650, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5016 p hg
    simpa only [d650, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
