/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons007
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare1120 (p : Pattern) (guard : d915 p = 1) : d53 p ≤ (0 : Int) + d53 p := by
  omega
theorem compare1121 (p : Pattern) (guard : d984 p = 1) : d57 p ≤ (0 : Int) + d295 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d57, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1120 p hg
    simpa only [d984, d57, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d57, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare797 p hg
    simpa only [d984, d57, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1122 (p : Pattern) (guard : d0 p = 1) : d59 p ≤ (0 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1123 (p : Pattern) (guard : d915 p = 1) : d60 p ≤ (0 : Int) + d53 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare796 p hg
    simpa only [d915, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1122 p hg
    simpa only [d915, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1124 (p : Pattern) (guard : d0 p = 1) : d63 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1125 (p : Pattern) (guard : d984 p = 1) : d64 p ≤ (0 : Int) + d295 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d64, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1123 p hg
    simpa only [d984, d64, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d64, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1124 p hg
    simpa only [d984, d64, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1126 (p : Pattern) (guard : d984 p = 1) : d65 p ≤ (0 : Int) + d295 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1121 p hg
    simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1125 p hg
    simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1127 (p : Pattern) (guard : d984 p = 1) : d66 p ≤ (0 : Int) + d296 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d66, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1119 p hg
    simpa only [d66, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d66, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1126 p hg
    simpa only [d66, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1128 (p : Pattern) (guard : d984 p = 1) : d67 p ≤ (0 : Int) + d297 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d67, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1112 p hg
    simpa only [d67, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d67, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1127 p hg
    simpa only [d67, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1129 (p : Pattern) (guard : d0 p = 1) : d26 p ≤ (0 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1130 (p : Pattern) (guard : d915 p = 1) : d27 p ≤ (0 : Int) + d16 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare787 p hg
    simpa only [d915, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1129 p hg
    simpa only [d915, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1131 (p : Pattern) (guard : d0 p = 1) : d72 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1132 (p : Pattern) (guard : d984 p = 1) : d73 p ≤ (0 : Int) + d293 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d73, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d984, d73, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d73, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1131 p hg
    simpa only [d984, d73, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1133 (p : Pattern) (guard : d984 p = 1) : d74 p ≤ (0 : Int) + d293 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1107 p hg
    simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1134 (p : Pattern) (guard : d0 p = 1) : d75 p ≤ (0 : Int) + d148 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1135 (p : Pattern) (guard : d984 p = 1) : d76 p ≤ (0 : Int) + d298 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d76, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d984, d76, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d76, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1134 p hg
    simpa only [d984, d76, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1136 (p : Pattern) (guard : d984 p = 1) : d77 p ≤ (0 : Int) + d299 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d77, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1107 p hg
    simpa only [d77, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d77, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1135 p hg
    simpa only [d77, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1137 (p : Pattern) (guard : d984 p = 1) : d78 p ≤ (0 : Int) + d300 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d78, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d78, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d78, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1136 p hg
    simpa only [d78, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1138 (p : Pattern) (guard : d0 p = 1) : d25 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1139 (p : Pattern) (guard : d915 p = 1) : d46 p ≤ (0 : Int) + d15 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d915, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1138 p hg
    simpa only [d915, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1140 (p : Pattern) (guard : d0 p = 1) : d75 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1141 (p : Pattern) (guard : d984 p = 1) : d79 p ≤ (0 : Int) + d294 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d79, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1139 p hg
    simpa only [d984, d79, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d79, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d984, d79, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1142 (p : Pattern) (guard : d984 p = 1) : d80 p ≤ (0 : Int) + d294 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1114 p hg
    simpa only [d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1141 p hg
    simpa only [d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1143 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1144 (p : Pattern) (guard : d915 p = 1) : d56 p ≤ (0 : Int) + d53 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare796 p hg
    simpa only [d915, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1143 p hg
    simpa only [d915, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1145 (p : Pattern) (guard : d984 p = 1) : d81 p ≤ (0 : Int) + d295 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d81, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1144 p hg
    simpa only [d984, d81, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d81, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d984, d81, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1146 (p : Pattern) (guard : d984 p = 1) : d82 p ≤ (0 : Int) + d295 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1121 p hg
    simpa only [d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1145 p hg
    simpa only [d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1147 (p : Pattern) (guard : d984 p = 1) : d83 p ≤ (0 : Int) + d296 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d83, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1142 p hg
    simpa only [d83, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d83, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1146 p hg
    simpa only [d83, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1148 (p : Pattern) (guard : d984 p = 1) : d84 p ≤ (0 : Int) + d301 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d84, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1137 p hg
    simpa only [d84, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d84, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1147 p hg
    simpa only [d84, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1149 (p : Pattern) (guard : d984 p = 1) : d85 p ≤ (0 : Int) + d302 p := by
  cases selected : p 106 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d85, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d85, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d85, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1148 p hg
    simpa only [d85, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1150 (p : Pattern) (guard : d915 p = 1) : d86 p ≤ (0 : Int) + d86 p := by
  omega
theorem compare1151 (p : Pattern) (guard : d984 p = 1) : d89 p ≤ (0 : Int) + d303 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d89, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1150 p hg
    simpa only [d984, d89, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d89, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare806 p hg
    simpa only [d984, d89, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1152 (p : Pattern) (guard : d0 p = 1) : d90 p ≤ (0 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1153 (p : Pattern) (guard : d915 p = 1) : d91 p ≤ (0 : Int) + d86 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d915, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1152 p hg
    simpa only [d915, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1154 (p : Pattern) (guard : d0 p = 1) : d93 p ≤ (0 : Int) + d148 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1155 (p : Pattern) (guard : d984 p = 1) : d94 p ≤ (0 : Int) + d304 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d94, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1153 p hg
    simpa only [d984, d94, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d94, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1154 p hg
    simpa only [d984, d94, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1156 (p : Pattern) (guard : d984 p = 1) : d95 p ≤ (0 : Int) + d305 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d95, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1151 p hg
    simpa only [d95, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d95, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1155 p hg
    simpa only [d95, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1157 (p : Pattern) (guard : d984 p = 1) : d96 p ≤ (0 : Int) + d306 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d96, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1112 p hg
    simpa only [d96, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d96, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d96, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1158 (p : Pattern) (guard : d915 p = 1) : d98 p ≤ (0 : Int) + d98 p := by
  omega
theorem compare1159 (p : Pattern) (guard : d984 p = 1) : d100 p ≤ (0 : Int) + d307 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d100, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1158 p hg
    simpa only [d984, d100, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d100, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare812 p hg
    simpa only [d984, d100, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1160 (p : Pattern) (guard : d0 p = 1) : d71 p ≤ (0 : Int) + d98 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1161 (p : Pattern) (guard : d915 p = 1) : d99 p ≤ (0 : Int) + d98 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare811 p hg
    simpa only [d915, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1160 p hg
    simpa only [d915, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1162 (p : Pattern) (guard : d0 p = 1) : d72 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1163 (p : Pattern) (guard : d984 p = 1) : d101 p ≤ (0 : Int) + d307 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d101, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1161 p hg
    simpa only [d984, d101, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d101, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1162 p hg
    simpa only [d984, d101, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1164 (p : Pattern) (guard : d984 p = 1) : d102 p ≤ (0 : Int) + d307 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1159 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1163 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1165 (p : Pattern) (guard : d984 p = 1) : d103 p ≤ (0 : Int) + d308 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d103, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1157 p hg
    simpa only [d103, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d103, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1164 p hg
    simpa only [d103, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1166 (p : Pattern) (guard : d984 p = 1) : d89 p ≤ (0 : Int) + d304 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d89, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1150 p hg
    simpa only [d984, d89, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d89, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare826 p hg
    simpa only [d984, d89, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1167 (p : Pattern) (guard : d0 p = 1) : d87 p ≤ (0 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1168 (p : Pattern) (guard : d915 p = 1) : d88 p ≤ (0 : Int) + d86 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d915, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1167 p hg
    simpa only [d915, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1169 (p : Pattern) (guard : d984 p = 1) : d104 p ≤ (0 : Int) + d309 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d104, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1168 p hg
    simpa only [d984, d104, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d104, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d984, d104, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1170 (p : Pattern) (guard : d984 p = 1) : d105 p ≤ (0 : Int) + d310 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d105, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1166 p hg
    simpa only [d105, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d105, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1169 p hg
    simpa only [d105, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1171 (p : Pattern) (guard : d984 p = 1) : d106 p ≤ (0 : Int) + d311 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d106, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1136 p hg
    simpa only [d106, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d106, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1170 p hg
    simpa only [d106, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1172 (p : Pattern) (guard : d984 p = 1) : d107 p ≤ (0 : Int) + d307 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d107, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1161 p hg
    simpa only [d984, d107, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d107, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d984, d107, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1173 (p : Pattern) (guard : d984 p = 1) : d108 p ≤ (0 : Int) + d307 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1159 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1172 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1174 (p : Pattern) (guard : d915 p = 1) : d97 p ≤ (0 : Int) + d97 p := by
  omega
theorem compare1175 (p : Pattern) (guard : d984 p = 1) : d110 p ≤ (0 : Int) + d312 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d110, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1174 p hg
    simpa only [d984, d110, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d110, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare832 p hg
    simpa only [d984, d110, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1176 (p : Pattern) (guard : d0 p = 1) : d70 p ≤ (0 : Int) + d97 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1177 (p : Pattern) (guard : d915 p = 1) : d109 p ≤ (0 : Int) + d97 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare831 p hg
    simpa only [d915, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1176 p hg
    simpa only [d915, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1178 (p : Pattern) (guard : d984 p = 1) : d111 p ≤ (0 : Int) + d312 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d111, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1177 p hg
    simpa only [d984, d111, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d111, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d984, d111, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1179 (p : Pattern) (guard : d984 p = 1) : d112 p ≤ (0 : Int) + d312 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1175 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1178 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1180 (p : Pattern) (guard : d984 p = 1) : d113 p ≤ (0 : Int) + d313 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d113, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1173 p hg
    simpa only [d113, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d113, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1179 p hg
    simpa only [d113, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1181 (p : Pattern) (guard : d984 p = 1) : d114 p ≤ (0 : Int) + d314 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d114, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1171 p hg
    simpa only [d114, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d114, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1180 p hg
    simpa only [d114, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1182 (p : Pattern) (guard : d984 p = 1) : d115 p ≤ (0 : Int) + d315 p := by
  cases selected : p 106 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d115, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1165 p hg
    simpa only [d115, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d115, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d115, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1183 (p : Pattern) (guard : d984 p = 1) : d116 p ≤ (0 : Int) + d316 p := by
  cases selected : p 86 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d116, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1149 p hg
    simpa only [d116, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d116, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1182 p hg
    simpa only [d116, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1184 (p : Pattern) (guard : d0 p = 1) : d43 p ≤ (0 : Int) + d148 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1185 (p : Pattern) (guard : d984 p = 1) : d44 p ≤ (0 : Int) + d298 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d44, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1109 p hg
    simpa only [d984, d44, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d44, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1184 p hg
    simpa only [d984, d44, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1186 (p : Pattern) (guard : d984 p = 1) : d45 p ≤ (0 : Int) + d299 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d45, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1107 p hg
    simpa only [d45, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d45, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1185 p hg
    simpa only [d45, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1187 (p : Pattern) (guard : d984 p = 1) : d45 p ≤ (0 : Int) + d300 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1112 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1186 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1188 (p : Pattern) (guard : d984 p = 1) : d67 p ≤ (0 : Int) + d301 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d67, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1187 p hg
    simpa only [d67, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d67, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1127 p hg
    simpa only [d67, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1189 (p : Pattern) (guard : d0 p = 1) : d27 p ≤ (0 : Int) + d148 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1190 (p : Pattern) (guard : d984 p = 1) : d28 p ≤ (0 : Int) + d298 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d28, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1106 p hg
    simpa only [d984, d28, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d28, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1189 p hg
    simpa only [d984, d28, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1191 (p : Pattern) (guard : d984 p = 1) : d76 p ≤ (0 : Int) + d317 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d76, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d984, d76, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d76, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d984, d76, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1192 (p : Pattern) (guard : d984 p = 1) : d77 p ≤ (0 : Int) + d318 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d77, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1190 p hg
    simpa only [d77, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d77, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1191 p hg
    simpa only [d77, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1193 (p : Pattern) (guard : d984 p = 1) : d77 p ≤ (0 : Int) + d319 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1136 p hg
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1192 p hg
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1194 (p : Pattern) (guard : d984 p = 1) : d117 p ≤ (0 : Int) + d320 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d117, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1193 p hg
    simpa only [d117, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d117, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1147 p hg
    simpa only [d117, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1195 (p : Pattern) (guard : d984 p = 1) : d118 p ≤ (0 : Int) + d321 p := by
  cases selected : p 106 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d118, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1188 p hg
    simpa only [d118, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d118, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1194 p hg
    simpa only [d118, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1196 (p : Pattern) (guard : d0 p = 1) : d120 p ≤ (0 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1197 (p : Pattern) (guard : d915 p = 1) : d121 p ≤ (0 : Int) + d86 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d915, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1196 p hg
    simpa only [d915, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1198 (p : Pattern) (guard : d0 p = 1) : d93 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1199 (p : Pattern) (guard : d984 p = 1) : d122 p ≤ (0 : Int) + d309 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d122, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1197 p hg
    simpa only [d984, d122, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d122, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1198 p hg
    simpa only [d984, d122, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1200 (p : Pattern) (guard : d984 p = 1) : d123 p ≤ (0 : Int) + d310 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d123, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1166 p hg
    simpa only [d123, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d123, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1199 p hg
    simpa only [d123, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1201 (p : Pattern) (guard : d984 p = 1) : d124 p ≤ (0 : Int) + d311 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d124, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1186 p hg
    simpa only [d124, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d124, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1200 p hg
    simpa only [d124, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1202 (p : Pattern) (guard : d984 p = 1) : d125 p ≤ (0 : Int) + d312 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d125, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1177 p hg
    simpa only [d984, d125, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d125, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d984, d125, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1203 (p : Pattern) (guard : d984 p = 1) : d126 p ≤ (0 : Int) + d312 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1175 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1202 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1204 (p : Pattern) (guard : d984 p = 1) : d127 p ≤ (0 : Int) + d313 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d127, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1164 p hg
    simpa only [d127, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d127, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1203 p hg
    simpa only [d127, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1205 (p : Pattern) (guard : d984 p = 1) : d128 p ≤ (0 : Int) + d314 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d128, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1201 p hg
    simpa only [d128, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d128, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1204 p hg
    simpa only [d128, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1206 (p : Pattern) (guard : d984 p = 1) : d129 p ≤ (0 : Int) + d322 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d129, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1192 p hg
    simpa only [d129, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d129, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1146 p hg
    simpa only [d129, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1207 (p : Pattern) (guard : d984 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare1208 (p : Pattern) (guard : d984 p = 1) : d130 p ≤ (0 : Int) + d323 p := by
  cases selected : p 113 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d130, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1179 p hg
    simpa only [d130, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d130, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d130, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1209 (p : Pattern) (guard : d984 p = 1) : d131 p ≤ (0 : Int) + d324 p := by
  cases selected : p 112 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d131, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1206 p hg
    simpa only [d131, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d131, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1208 p hg
    simpa only [d131, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1210 (p : Pattern) (guard : d984 p = 1) : d132 p ≤ (0 : Int) + d325 p := by
  cases selected : p 106 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d132, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1205 p hg
    simpa only [d132, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d132, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1209 p hg
    simpa only [d132, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1211 (p : Pattern) (guard : d984 p = 1) : d133 p ≤ (0 : Int) + d326 p := by
  cases selected : p 86 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d133, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1195 p hg
    simpa only [d133, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d133, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1210 p hg
    simpa only [d133, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1212 (p : Pattern) (guard : d984 p = 1) : d134 p ≤ (0 : Int) + d327 p := by
  cases selected : p 80 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d134, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1183 p hg
    simpa only [d134, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d134, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1211 p hg
    simpa only [d134, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1213 (p : Pattern) (guard : d985 p = 1) : d0 p ≤ (0 : Int) + d0 p := by
  omega
theorem compare1214 (p : Pattern) (guard : d985 p = 1) : d3 p ≤ (0 : Int) + d2 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d985, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare660 p hg
    simpa only [d985, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d985, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d985, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1215 (p : Pattern) (guard : d985 p = 1) : d4 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d4, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1213 p hg
    simpa only [d4, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d4, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1214 p hg
    simpa only [d4, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1216 (p : Pattern) (guard : d985 p = 1) : d5 p ≤ (0 : Int) + d5 p := by
  omega
theorem compare1217 (p : Pattern) (guard : d985 p = 1) : d6 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1215 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1216 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1218 (p : Pattern) (guard : d985 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare1219 (p : Pattern) (guard : d985 p = 1) : d7 p ≤ (0 : Int) + d37 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d7, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1215 p hg
    simpa only [d7, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d7, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d7, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1220 (p : Pattern) (guard : d985 p = 1) : d8 p ≤ (0 : Int) + d697 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d8, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1217 p hg
    simpa only [d8, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d8, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1219 p hg
    simpa only [d8, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1221 (p : Pattern) (guard : d985 p = 1) : d1 p ≤ (0 : Int) + d1 p := by
  omega
theorem compare1222 (p : Pattern) (guard : d985 p = 1) : d9 p ≤ (0 : Int) + d2 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare222 p hg
    simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1223 (p : Pattern) (guard : d985 p = 1) : d10 p ≤ (0 : Int) + d11 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1221 p hg
    simpa only [d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1222 p hg
    simpa only [d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1224 (p : Pattern) (guard : d985 p = 1) : d11 p ≤ (0 : Int) + d11 p := by
  omega
theorem compare1225 (p : Pattern) (guard : d985 p = 1) : d12 p ≤ (0 : Int) + d11 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1223 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1224 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1226 (p : Pattern) (guard : d985 p = 1) : d13 p ≤ (0 : Int) + d39 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1223 p hg
    simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1227 (p : Pattern) (guard : d985 p = 1) : d14 p ≤ (0 : Int) + d698 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d14, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1225 p hg
    simpa only [d14, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d14, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1226 p hg
    simpa only [d14, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1228 (p : Pattern) (guard : d985 p = 1) : d15 p ≤ (0 : Int) + d699 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d15, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1220 p hg
    simpa only [d15, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d15, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1227 p hg
    simpa only [d15, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1229 (p : Pattern) (guard : d985 p = 1) : d16 p ≤ (0 : Int) + d700 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d16, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1220 p hg
    simpa only [d16, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d16, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1228 p hg
    simpa only [d16, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1230 (p : Pattern) (guard : d985 p = 1) : d17 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1214 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1231 (p : Pattern) (guard : d985 p = 1) : d18 p ≤ (0 : Int) + d37 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d18, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1215 p hg
    simpa only [d18, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d18, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1230 p hg
    simpa only [d18, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1232 (p : Pattern) (guard : d985 p = 1) : d19 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1230 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1233 (p : Pattern) (guard : d985 p = 1) : d20 p ≤ (0 : Int) + d986 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d20, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1231 p hg
    simpa only [d20, d986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d20, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1232 p hg
    simpa only [d20, d986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1234 (p : Pattern) (guard : d985 p = 1) : d21 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1222 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1235 (p : Pattern) (guard : d985 p = 1) : d22 p ≤ (0 : Int) + d39 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d22, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1223 p hg
    simpa only [d22, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d22, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1234 p hg
    simpa only [d22, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1236 (p : Pattern) (guard : d985 p = 1) : d23 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1234 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1237 (p : Pattern) (guard : d985 p = 1) : d24 p ≤ (0 : Int) + d987 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d24, d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1235 p hg
    simpa only [d24, d987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d24, d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1236 p hg
    simpa only [d24, d987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1238 (p : Pattern) (guard : d985 p = 1) : d25 p ≤ (0 : Int) + d988 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d25, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1233 p hg
    simpa only [d25, d988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d25, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1237 p hg
    simpa only [d25, d988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1239 (p : Pattern) (guard : d985 p = 1) : d26 p ≤ (0 : Int) + d989 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d26, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1233 p hg
    simpa only [d26, d989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d26, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1238 p hg
    simpa only [d26, d989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1240 (p : Pattern) (guard : d985 p = 1) : d27 p ≤ (0 : Int) + d990 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d27, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1229 p hg
    simpa only [d27, d990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d27, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1239 p hg
    simpa only [d27, d990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1241 (p : Pattern) (guard : d985 p = 1) : d28 p ≤ (0 : Int) + d991 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d28, d991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1229 p hg
    simpa only [d28, d991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d28, d991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1240 p hg
    simpa only [d28, d991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1242 (p : Pattern) (guard : d0 p = 1) : d1 p ≤ (0 : Int) + d1 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1243 (p : Pattern) (guard : d985 p = 1) : d29 p ≤ (0 : Int) + d1 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d985, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare200 p hg
    simpa only [d985, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d985, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1242 p hg
    simpa only [d985, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1244 (p : Pattern) (guard : d985 p = 1) : d30 p ≤ (0 : Int) + d11 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d30, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1243 p hg
    simpa only [d30, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d30, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d30, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1245 (p : Pattern) (guard : d985 p = 1) : d31 p ≤ (0 : Int) + d992 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d31, d992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1215 p hg
    simpa only [d31, d992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d31, d992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1244 p hg
    simpa only [d31, d992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1246 (p : Pattern) (guard : d985 p = 1) : d32 p ≤ (0 : Int) + d39 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d32, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1244 p hg
    simpa only [d32, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d32, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d32, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1247 (p : Pattern) (guard : d985 p = 1) : d33 p ≤ (0 : Int) + d993 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d33, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1245 p hg
    simpa only [d33, d993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d33, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d33, d993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1248 (p : Pattern) (guard : d985 p = 1) : d34 p ≤ (0 : Int) + d994 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d34, d994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1247 p hg
    simpa only [d34, d994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d34, d994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1237 p hg
    simpa only [d34, d994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1249 (p : Pattern) (guard : d985 p = 1) : d35 p ≤ (0 : Int) + d995 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d35, d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1247 p hg
    simpa only [d35, d995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d35, d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1248 p hg
    simpa only [d35, d995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1250 (p : Pattern) (guard : d985 p = 1) : d36 p ≤ (0 : Int) + d996 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d36, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1229 p hg
    simpa only [d36, d996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d36, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1249 p hg
    simpa only [d36, d996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1251 (p : Pattern) (guard : d985 p = 1) : d37 p ≤ (0 : Int) + d37 p := by
  omega
theorem compare1252 (p : Pattern) (guard : d985 p = 1) : d38 p ≤ (0 : Int) + d697 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d38, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1217 p hg
    simpa only [d38, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d38, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1251 p hg
    simpa only [d38, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1253 (p : Pattern) (guard : d985 p = 1) : d39 p ≤ (0 : Int) + d39 p := by
  omega
theorem compare1254 (p : Pattern) (guard : d985 p = 1) : d40 p ≤ (0 : Int) + d698 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d40, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1225 p hg
    simpa only [d40, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d40, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1253 p hg
    simpa only [d40, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1255 (p : Pattern) (guard : d985 p = 1) : d41 p ≤ (0 : Int) + d699 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d41, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1252 p hg
    simpa only [d41, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d41, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1254 p hg
    simpa only [d41, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1256 (p : Pattern) (guard : d985 p = 1) : d42 p ≤ (0 : Int) + d700 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d42, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1252 p hg
    simpa only [d42, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d42, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1255 p hg
    simpa only [d42, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1257 (p : Pattern) (guard : d985 p = 1) : d43 p ≤ (0 : Int) + d990 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d43, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1256 p hg
    simpa only [d43, d990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d43, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1239 p hg
    simpa only [d43, d990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1258 (p : Pattern) (guard : d985 p = 1) : d44 p ≤ (0 : Int) + d997 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d44, d997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1250 p hg
    simpa only [d44, d997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d44, d997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1257 p hg
    simpa only [d44, d997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1259 (p : Pattern) (guard : d985 p = 1) : d45 p ≤ (0 : Int) + d998 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d45, d998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1241 p hg
    simpa only [d45, d998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d45, d998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1258 p hg
    simpa only [d45, d998, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
