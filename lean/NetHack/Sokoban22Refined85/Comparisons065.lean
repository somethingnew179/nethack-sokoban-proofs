/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons064
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare9100 (p : Pattern) (guard : d1 p = 1) : d269 p ≤ (0 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d269, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9099 p hg
    simpa only [d269, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d269, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1397 p hg
    simpa only [d269, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9101 (p : Pattern) (guard : d1 p = 1) : d1133 p ≤ (0 : Int) + d132 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9100 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9102 (p : Pattern) (guard : d4395 p = 1) : d1134 p ≤ (0 : Int) + d245 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1134, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9101 p hg
    simpa only [d4395, d1134, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1134, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8862 p hg
    simpa only [d4395, d1134, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9103 (p : Pattern) (guard : d4617 p = 1) : d1135 p ≤ (0 : Int) + d245 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9098 p hg
    simpa only [d4617, d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9102 p hg
    simpa only [d4617, d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9104 (p : Pattern) (guard : d0 p = 1) : d1062 p ≤ (0 : Int) + d245 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9105 (p : Pattern) (guard : d4618 p = 1) : d1136 p ≤ (0 : Int) + d245 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9103 p hg
    simpa only [d4618, d1136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9104 p hg
    simpa only [d4618, d1136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9106 (p : Pattern) (guard : d0 p = 1) : d1061 p ≤ (0 : Int) + d933 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9107 (p : Pattern) (guard : d1 p = 1) : d282 p ≤ (0 : Int) + d107 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1346 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9108 (p : Pattern) (guard : d1 p = 1) : d108 p ≤ (0 : Int) + d108 p := by
  omega
theorem compare9109 (p : Pattern) (guard : d1 p = 1) : d298 p ≤ (0 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d298, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9107 p hg
    simpa only [d298, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d298, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9108 p hg
    simpa only [d298, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9110 (p : Pattern) (guard : d1 p = 1) : d1137 p ≤ (0 : Int) + d109 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9109 p hg
    simpa only [d1137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2371 p hg
    simpa only [d1137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9111 (p : Pattern) (guard : d4395 p = 1) : d1138 p ≤ (0 : Int) + d933 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1138, d933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9110 p hg
    simpa only [d4395, d1138, d933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1138, d933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8800 p hg
    simpa only [d4395, d1138, d933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9112 (p : Pattern) (guard : d4617 p = 1) : d1139 p ≤ (0 : Int) + d933 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d1139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9106 p hg
    simpa only [d4617, d1139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d1139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9111 p hg
    simpa only [d4617, d1139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9113 (p : Pattern) (guard : d0 p = 1) : d1141 p ≤ (0 : Int) + d933 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9114 (p : Pattern) (guard : d4618 p = 1) : d1142 p ≤ (0 : Int) + d933 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9112 p hg
    simpa only [d4618, d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9113 p hg
    simpa only [d4618, d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9115 (p : Pattern) (guard : d4618 p = 1) : d1143 p ≤ (0 : Int) + d4788 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1143, d4788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9105 p hg
    simpa only [d1143, d4788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1143, d4788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9114 p hg
    simpa only [d1143, d4788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9116 (p : Pattern) (guard : d4618 p = 1) : d1144 p ≤ (0 : Int) + d4789 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1144, d4789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9097 p hg
    simpa only [d1144, d4789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1144, d4789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9115 p hg
    simpa only [d1144, d4789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9117 (p : Pattern) (guard : d0 p = 1) : d1089 p ≤ (0 : Int) + d939 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9118 (p : Pattern) (guard : d4395 p = 1) : d1134 p ≤ (0 : Int) + d939 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1134, d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9101 p hg
    simpa only [d4395, d1134, d939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1134, d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8902 p hg
    simpa only [d4395, d1134, d939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9119 (p : Pattern) (guard : d4617 p = 1) : d1135 p ≤ (0 : Int) + d939 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9117 p hg
    simpa only [d4617, d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9118 p hg
    simpa only [d4617, d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9120 (p : Pattern) (guard : d0 p = 1) : d1062 p ≤ (0 : Int) + d939 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9121 (p : Pattern) (guard : d4618 p = 1) : d1136 p ≤ (0 : Int) + d939 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9119 p hg
    simpa only [d4618, d1136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9120 p hg
    simpa only [d4618, d1136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9122 (p : Pattern) (guard : d4618 p = 1) : d1143 p ≤ (0 : Int) + d4790 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1143, d4790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9121 p hg
    simpa only [d1143, d4790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1143, d4790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9114 p hg
    simpa only [d1143, d4790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9123 (p : Pattern) (guard : d4618 p = 1) : d1145 p ≤ (0 : Int) + d4791 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1145, d4791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9122 p hg
    simpa only [d1145, d4791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1145, d4791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8975 p hg
    simpa only [d1145, d4791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9124 (p : Pattern) (guard : d4618 p = 1) : d1146 p ≤ (0 : Int) + d4792 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1146, d4792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9116 p hg
    simpa only [d1146, d4792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1146, d4792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9123 p hg
    simpa only [d1146, d4792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9125 (p : Pattern) (guard : d4618 p = 1) : d1147 p ≤ (0 : Int) + d4793 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1147, d4793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9086 p hg
    simpa only [d1147, d4793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1147, d4793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9124 p hg
    simpa only [d1147, d4793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9126 (p : Pattern) (guard : d4618 p = 1) : d1148 p ≤ (0 : Int) + d4794 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1148, d4794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8978 p hg
    simpa only [d1148, d4794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1148, d4794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9125 p hg
    simpa only [d1148, d4794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9127 (p : Pattern) (guard : d4618 p = 1) : d1149 p ≤ (0 : Int) + d4795 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1149, d4795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9078 p hg
    simpa only [d1149, d4795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1149, d4795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9126 p hg
    simpa only [d1149, d4795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9128 (p : Pattern) (guard : d4618 p = 1) : d1150 p ≤ (0 : Int) + d4796 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1150, d4796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9061 p hg
    simpa only [d1150, d4796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1150, d4796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9127 p hg
    simpa only [d1150, d4796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9129 (p : Pattern) (guard : d4397 p = 1) : d949 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d949, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4212 p hg
    simpa only [d4397, d949, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d949, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7784 p hg
    simpa only [d4397, d949, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9130 (p : Pattern) (guard : d0 p = 1) : d33 p ≤ (0 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9131 (p : Pattern) (guard : d4148 p = 1) : d950 p ≤ (0 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d950, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d950, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d950, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9130 p hg
    simpa only [d4148, d950, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9132 (p : Pattern) (guard : d4397 p = 1) : d951 p ≤ (0 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d951, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9131 p hg
    simpa only [d4397, d951, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d951, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7787 p hg
    simpa only [d4397, d951, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9133 (p : Pattern) (guard : d4397 p = 1) : d952 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d952, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9129 p hg
    simpa only [d952, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d952, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9132 p hg
    simpa only [d952, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9134 (p : Pattern) (guard : d0 p = 1) : d33 p ≤ (0 : Int) + d37 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9135 (p : Pattern) (guard : d4148 p = 1) : d33 p ≤ (0 : Int) + d38 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4148, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9134 p hg
    simpa only [d4148, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9136 (p : Pattern) (guard : d4397 p = 1) : d953 p ≤ (0 : Int) + d45 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d953, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9135 p hg
    simpa only [d4397, d953, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d953, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7790 p hg
    simpa only [d4397, d953, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9137 (p : Pattern) (guard : d4397 p = 1) : d954 p ≤ (0 : Int) + d50 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d954, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4220 p hg
    simpa only [d4397, d954, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d954, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7793 p hg
    simpa only [d4397, d954, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9138 (p : Pattern) (guard : d4397 p = 1) : d955 p ≤ (0 : Int) + d51 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d955, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9136 p hg
    simpa only [d955, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d955, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9137 p hg
    simpa only [d955, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9139 (p : Pattern) (guard : d4397 p = 1) : d956 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d956, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9133 p hg
    simpa only [d956, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d956, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9138 p hg
    simpa only [d956, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9140 (p : Pattern) (guard : d0 p = 1) : d963 p ≤ (0 : Int) + d392 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9141 (p : Pattern) (guard : d4398 p = 1) : d964 p ≤ (0 : Int) + d653 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d964, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9139 p hg
    simpa only [d4398, d964, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d964, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9140 p hg
    simpa only [d4398, d964, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9142 (p : Pattern) (guard : d4397 p = 1) : d965 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d965, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4212 p hg
    simpa only [d4397, d965, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d965, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7810 p hg
    simpa only [d4397, d965, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9143 (p : Pattern) (guard : d0 p = 1) : d53 p ≤ (0 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9144 (p : Pattern) (guard : d4148 p = 1) : d54 p ≤ (0 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d54, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d54, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d54, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9143 p hg
    simpa only [d4148, d54, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9145 (p : Pattern) (guard : d4397 p = 1) : d966 p ≤ (0 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d966, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9144 p hg
    simpa only [d4397, d966, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d966, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7812 p hg
    simpa only [d4397, d966, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9146 (p : Pattern) (guard : d4397 p = 1) : d967 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d967, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9142 p hg
    simpa only [d967, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d967, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9145 p hg
    simpa only [d967, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9147 (p : Pattern) (guard : d0 p = 1) : d53 p ≤ (0 : Int) + d78 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9148 (p : Pattern) (guard : d4148 p = 1) : d53 p ≤ (0 : Int) + d79 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4148, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9147 p hg
    simpa only [d4148, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9149 (p : Pattern) (guard : d4397 p = 1) : d968 p ≤ (0 : Int) + d80 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d968, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9148 p hg
    simpa only [d4397, d968, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d968, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7815 p hg
    simpa only [d4397, d968, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9150 (p : Pattern) (guard : d4397 p = 1) : d969 p ≤ (0 : Int) + d81 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d969, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9149 p hg
    simpa only [d969, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d969, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d969, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9151 (p : Pattern) (guard : d4397 p = 1) : d970 p ≤ (0 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d970, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9146 p hg
    simpa only [d970, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d970, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9150 p hg
    simpa only [d970, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9152 (p : Pattern) (guard : d0 p = 1) : d975 p ≤ (0 : Int) + d399 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9153 (p : Pattern) (guard : d4398 p = 1) : d976 p ≤ (0 : Int) + d654 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d976, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9151 p hg
    simpa only [d4398, d976, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d976, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9152 p hg
    simpa only [d4398, d976, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9154 (p : Pattern) (guard : d4398 p = 1) : d977 p ≤ (0 : Int) + d655 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d977, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9141 p hg
    simpa only [d977, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d977, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9153 p hg
    simpa only [d977, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9155 (p : Pattern) (guard : d4397 p = 1) : d978 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d978, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4212 p hg
    simpa only [d4397, d978, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d978, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7828 p hg
    simpa only [d4397, d978, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9156 (p : Pattern) (guard : d4397 p = 1) : d979 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d979, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9155 p hg
    simpa only [d979, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d979, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9145 p hg
    simpa only [d979, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9157 (p : Pattern) (guard : d4397 p = 1) : d980 p ≤ (0 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d980, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9156 p hg
    simpa only [d980, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d980, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9150 p hg
    simpa only [d980, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9158 (p : Pattern) (guard : d0 p = 1) : d983 p ≤ (0 : Int) + d407 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9159 (p : Pattern) (guard : d4398 p = 1) : d984 p ≤ (0 : Int) + d656 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d984, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9157 p hg
    simpa only [d4398, d984, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d984, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9158 p hg
    simpa only [d4398, d984, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9160 (p : Pattern) (guard : d4397 p = 1) : d985 p ≤ (0 : Int) + d90 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d985, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4246 p hg
    simpa only [d4397, d985, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d985, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7815 p hg
    simpa only [d4397, d985, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9161 (p : Pattern) (guard : d4397 p = 1) : d986 p ≤ (0 : Int) + d92 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d986, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9160 p hg
    simpa only [d986, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d986, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4248 p hg
    simpa only [d986, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9162 (p : Pattern) (guard : d4397 p = 1) : d987 p ≤ (0 : Int) + d94 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d987, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9161 p hg
    simpa only [d987, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d987, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4250 p hg
    simpa only [d987, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9163 (p : Pattern) (guard : d4398 p = 1) : d988 p ≤ (0 : Int) + d657 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d988, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9162 p hg
    simpa only [d4398, d988, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d988, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2241 p hg
    simpa only [d4398, d988, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9164 (p : Pattern) (guard : d4398 p = 1) : d989 p ≤ (0 : Int) + d658 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d989, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9159 p hg
    simpa only [d989, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d989, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9163 p hg
    simpa only [d989, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9165 (p : Pattern) (guard : d4398 p = 1) : d990 p ≤ (0 : Int) + d659 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d990, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9154 p hg
    simpa only [d990, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d990, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9164 p hg
    simpa only [d990, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9166 (p : Pattern) (guard : d4397 p = 1) : d991 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d991, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4212 p hg
    simpa only [d4397, d991, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d991, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7846 p hg
    simpa only [d4397, d991, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9167 (p : Pattern) (guard : d4397 p = 1) : d992 p ≤ (0 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d992, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9131 p hg
    simpa only [d4397, d992, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d992, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7812 p hg
    simpa only [d4397, d992, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9168 (p : Pattern) (guard : d4397 p = 1) : d993 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d993, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9166 p hg
    simpa only [d993, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d993, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9167 p hg
    simpa only [d993, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9169 (p : Pattern) (guard : d4397 p = 1) : d994 p ≤ (0 : Int) + d45 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d994, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9135 p hg
    simpa only [d4397, d994, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d994, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7850 p hg
    simpa only [d4397, d994, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9170 (p : Pattern) (guard : d4397 p = 1) : d995 p ≤ (0 : Int) + d51 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d995, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9169 p hg
    simpa only [d995, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d995, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9137 p hg
    simpa only [d995, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9171 (p : Pattern) (guard : d4397 p = 1) : d996 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d996, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9168 p hg
    simpa only [d996, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d996, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9170 p hg
    simpa only [d996, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9172 (p : Pattern) (guard : d0 p = 1) : d999 p ≤ (0 : Int) + d397 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9173 (p : Pattern) (guard : d4398 p = 1) : d1000 p ≤ (0 : Int) + d660 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d1000, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9171 p hg
    simpa only [d4398, d1000, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d1000, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9172 p hg
    simpa only [d4398, d1000, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9174 (p : Pattern) (guard : d4397 p = 1) : d1001 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1001, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4212 p hg
    simpa only [d4397, d1001, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1001, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7860 p hg
    simpa only [d4397, d1001, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9175 (p : Pattern) (guard : d4397 p = 1) : d1002 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1002, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9174 p hg
    simpa only [d1002, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1002, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9145 p hg
    simpa only [d1002, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9176 (p : Pattern) (guard : d4397 p = 1) : d1003 p ≤ (0 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1003, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9175 p hg
    simpa only [d1003, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1003, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9150 p hg
    simpa only [d1003, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9177 (p : Pattern) (guard : d0 p = 1) : d1005 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9178 (p : Pattern) (guard : d4398 p = 1) : d1006 p ≤ (0 : Int) + d661 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d1006, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9176 p hg
    simpa only [d4398, d1006, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d1006, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9177 p hg
    simpa only [d4398, d1006, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9179 (p : Pattern) (guard : d4398 p = 1) : d1007 p ≤ (0 : Int) + d662 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1007, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9173 p hg
    simpa only [d1007, d662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1007, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9178 p hg
    simpa only [d1007, d662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9180 (p : Pattern) (guard : d4397 p = 1) : d1008 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1008, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4212 p hg
    simpa only [d4397, d1008, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1008, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7870 p hg
    simpa only [d4397, d1008, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9181 (p : Pattern) (guard : d4397 p = 1) : d1009 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1009, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9180 p hg
    simpa only [d1009, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1009, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9145 p hg
    simpa only [d1009, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9182 (p : Pattern) (guard : d4397 p = 1) : d1010 p ≤ (0 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1010, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9181 p hg
    simpa only [d1010, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1010, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9150 p hg
    simpa only [d1010, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9183 (p : Pattern) (guard : d0 p = 1) : d1005 p ≤ (0 : Int) + d410 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9184 (p : Pattern) (guard : d4398 p = 1) : d1011 p ≤ (0 : Int) + d663 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d1011, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9182 p hg
    simpa only [d4398, d1011, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d1011, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9183 p hg
    simpa only [d4398, d1011, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9185 (p : Pattern) (guard : d4398 p = 1) : d1012 p ≤ (0 : Int) + d664 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1012, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9184 p hg
    simpa only [d1012, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1012, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4278 p hg
    simpa only [d1012, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9186 (p : Pattern) (guard : d4398 p = 1) : d1013 p ≤ (0 : Int) + d665 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1013, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9179 p hg
    simpa only [d1013, d665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1013, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9185 p hg
    simpa only [d1013, d665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9187 (p : Pattern) (guard : d4398 p = 1) : d1014 p ≤ (0 : Int) + d666 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1014, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9165 p hg
    simpa only [d1014, d666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1014, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9186 p hg
    simpa only [d1014, d666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9188 (p : Pattern) (guard : d4397 p = 1) : d1015 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1015, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4212 p hg
    simpa only [d4397, d1015, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1015, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7878 p hg
    simpa only [d4397, d1015, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9189 (p : Pattern) (guard : d4397 p = 1) : d1016 p ≤ (0 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1016, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9131 p hg
    simpa only [d4397, d1016, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1016, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7880 p hg
    simpa only [d4397, d1016, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9190 (p : Pattern) (guard : d4397 p = 1) : d1017 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1017, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9188 p hg
    simpa only [d1017, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1017, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9189 p hg
    simpa only [d1017, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9191 (p : Pattern) (guard : d4397 p = 1) : d1018 p ≤ (0 : Int) + d45 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1018, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9135 p hg
    simpa only [d4397, d1018, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1018, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7883 p hg
    simpa only [d4397, d1018, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9192 (p : Pattern) (guard : d4397 p = 1) : d1019 p ≤ (0 : Int) + d51 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1019, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9191 p hg
    simpa only [d1019, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1019, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9137 p hg
    simpa only [d1019, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9193 (p : Pattern) (guard : d4397 p = 1) : d1020 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1020, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9190 p hg
    simpa only [d1020, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1020, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9192 p hg
    simpa only [d1020, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9194 (p : Pattern) (guard : d0 p = 1) : d1023 p ≤ (0 : Int) + d418 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9195 (p : Pattern) (guard : d4398 p = 1) : d1024 p ≤ (0 : Int) + d667 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d1024, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9193 p hg
    simpa only [d4398, d1024, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d1024, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9194 p hg
    simpa only [d4398, d1024, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9196 (p : Pattern) (guard : d4397 p = 1) : d1025 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1025, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4212 p hg
    simpa only [d4397, d1025, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1025, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7892 p hg
    simpa only [d4397, d1025, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9197 (p : Pattern) (guard : d4397 p = 1) : d1026 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1026, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9196 p hg
    simpa only [d1026, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1026, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9145 p hg
    simpa only [d1026, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9198 (p : Pattern) (guard : d4397 p = 1) : d1027 p ≤ (0 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1027, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9197 p hg
    simpa only [d1027, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1027, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9150 p hg
    simpa only [d1027, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9199 (p : Pattern) (guard : d0 p = 1) : d1005 p ≤ (0 : Int) + d420 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9200 (p : Pattern) (guard : d4398 p = 1) : d1028 p ≤ (0 : Int) + d668 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d1028, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9198 p hg
    simpa only [d4398, d1028, d668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d1028, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9199 p hg
    simpa only [d4398, d1028, d668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9201 (p : Pattern) (guard : d4398 p = 1) : d1029 p ≤ (0 : Int) + d669 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1029, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9195 p hg
    simpa only [d1029, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1029, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9200 p hg
    simpa only [d1029, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9202 (p : Pattern) (guard : d4398 p = 1) : d988 p ≤ (0 : Int) + d670 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d988, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9162 p hg
    simpa only [d4398, d988, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d988, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2260 p hg
    simpa only [d4398, d988, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9203 (p : Pattern) (guard : d4398 p = 1) : d1030 p ≤ (0 : Int) + d671 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1030, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9153 p hg
    simpa only [d1030, d671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1030, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9202 p hg
    simpa only [d1030, d671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9204 (p : Pattern) (guard : d4398 p = 1) : d1031 p ≤ (0 : Int) + d672 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1031, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9201 p hg
    simpa only [d1031, d672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1031, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9203 p hg
    simpa only [d1031, d672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9205 (p : Pattern) (guard : d4397 p = 1) : d1032 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1032, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9155 p hg
    simpa only [d1032, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1032, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9167 p hg
    simpa only [d1032, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9206 (p : Pattern) (guard : d4397 p = 1) : d1033 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1033, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9205 p hg
    simpa only [d1033, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1033, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9170 p hg
    simpa only [d1033, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9207 (p : Pattern) (guard : d0 p = 1) : d1035 p ≤ (0 : Int) + d407 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9208 (p : Pattern) (guard : d4398 p = 1) : d1036 p ≤ (0 : Int) + d673 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d1036, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9206 p hg
    simpa only [d4398, d1036, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d1036, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9207 p hg
    simpa only [d4398, d1036, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9209 (p : Pattern) (guard : d0 p = 1) : d1005 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9210 (p : Pattern) (guard : d4398 p = 1) : d1006 p ≤ (0 : Int) + d674 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d1006, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9176 p hg
    simpa only [d4398, d1006, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d1006, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9209 p hg
    simpa only [d4398, d1006, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9211 (p : Pattern) (guard : d4398 p = 1) : d1037 p ≤ (0 : Int) + d675 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1037, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9208 p hg
    simpa only [d1037, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1037, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9210 p hg
    simpa only [d1037, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9212 (p : Pattern) (guard : d4398 p = 1) : d1038 p ≤ (0 : Int) + d676 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1038, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9178 p hg
    simpa only [d1038, d676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1038, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4278 p hg
    simpa only [d1038, d676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9213 (p : Pattern) (guard : d4398 p = 1) : d1039 p ≤ (0 : Int) + d677 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1039, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9211 p hg
    simpa only [d1039, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1039, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9212 p hg
    simpa only [d1039, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9214 (p : Pattern) (guard : d4398 p = 1) : d1040 p ≤ (0 : Int) + d678 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1040, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9204 p hg
    simpa only [d1040, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1040, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9213 p hg
    simpa only [d1040, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9215 (p : Pattern) (guard : d4398 p = 1) : d1041 p ≤ (0 : Int) + d679 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4398 p = 1 := by simpa only [d1041, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9187 p hg
    simpa only [d1041, d679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4398 p = 1 := by simpa only [d1041, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9214 p hg
    simpa only [d1041, d679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9216 (p : Pattern) (guard : d4397 p = 1) : d1042 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1042, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4314 p hg
    simpa only [d4397, d1042, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1042, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7910 p hg
    simpa only [d4397, d1042, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9217 (p : Pattern) (guard : d0 p = 1) : d118 p ≤ (0 : Int) + d109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9218 (p : Pattern) (guard : d4148 p = 1) : d1043 p ≤ (0 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d1043, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d1043, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d1043, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9217 p hg
    simpa only [d4148, d1043, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9219 (p : Pattern) (guard : d4397 p = 1) : d1044 p ≤ (0 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1044, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9218 p hg
    simpa only [d4397, d1044, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1044, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7913 p hg
    simpa only [d4397, d1044, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9220 (p : Pattern) (guard : d4397 p = 1) : d1045 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1045, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9216 p hg
    simpa only [d1045, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1045, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9219 p hg
    simpa only [d1045, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9221 (p : Pattern) (guard : d0 p = 1) : d118 p ≤ (0 : Int) + d122 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9222 (p : Pattern) (guard : d4148 p = 1) : d118 p ≤ (0 : Int) + d123 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3757 p hg
    simpa only [d4148, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9221 p hg
    simpa only [d4148, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9223 (p : Pattern) (guard : d4397 p = 1) : d1046 p ≤ (0 : Int) + d127 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1046, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9222 p hg
    simpa only [d4397, d1046, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1046, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7916 p hg
    simpa only [d4397, d1046, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9224 (p : Pattern) (guard : d4397 p = 1) : d1047 p ≤ (0 : Int) + d129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1047, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4128 p hg
    simpa only [d4397, d1047, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1047, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7919 p hg
    simpa only [d4397, d1047, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9225 (p : Pattern) (guard : d4397 p = 1) : d1048 p ≤ (0 : Int) + d130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1048, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9223 p hg
    simpa only [d1048, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1048, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9224 p hg
    simpa only [d1048, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9226 (p : Pattern) (guard : d4397 p = 1) : d1049 p ≤ (0 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1049, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9220 p hg
    simpa only [d1049, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1049, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9225 p hg
    simpa only [d1049, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9227 (p : Pattern) (guard : d0 p = 1) : d1056 p ≤ (0 : Int) + d418 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9228 (p : Pattern) (guard : d4398 p = 1) : d1057 p ≤ (0 : Int) + d680 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d4398, d1057, d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9226 p hg
    simpa only [d4398, d1057, d680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4398, d1057, d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9227 p hg
    simpa only [d4398, d1057, d680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9229 (p : Pattern) (guard : d4397 p = 1) : d1058 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1058, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4314 p hg
    simpa only [d4397, d1058, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1058, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d4397, d1058, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9230 (p : Pattern) (guard : d0 p = 1) : d132 p ≤ (0 : Int) + d109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9231 (p : Pattern) (guard : d4148 p = 1) : d133 p ≤ (0 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d133, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d133, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d133, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9230 p hg
    simpa only [d4148, d133, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9232 (p : Pattern) (guard : d4397 p = 1) : d1059 p ≤ (0 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1059, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9231 p hg
    simpa only [d4397, d1059, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1059, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d4397, d1059, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9233 (p : Pattern) (guard : d4397 p = 1) : d1060 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1060, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9229 p hg
    simpa only [d1060, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1060, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9232 p hg
    simpa only [d1060, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9234 (p : Pattern) (guard : d0 p = 1) : d132 p ≤ (0 : Int) + d148 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9235 (p : Pattern) (guard : d4148 p = 1) : d132 p ≤ (0 : Int) + d149 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4148, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9234 p hg
    simpa only [d4148, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9236 (p : Pattern) (guard : d4397 p = 1) : d1061 p ≤ (0 : Int) + d150 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d4397, d1061, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9235 p hg
    simpa only [d4397, d1061, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4397, d1061, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4397, d1061, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9237 (p : Pattern) (guard : d4397 p = 1) : d1062 p ≤ (0 : Int) + d151 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1062, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9236 p hg
    simpa only [d1062, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1062, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d1062, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9238 (p : Pattern) (guard : d4397 p = 1) : d1063 p ≤ (0 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4397 p = 1 := by simpa only [d1063, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9233 p hg
    simpa only [d1063, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4397 p = 1 := by simpa only [d1063, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9237 p hg
    simpa only [d1063, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9239 (p : Pattern) (guard : d0 p = 1) : d1067 p ≤ (0 : Int) + d420 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
