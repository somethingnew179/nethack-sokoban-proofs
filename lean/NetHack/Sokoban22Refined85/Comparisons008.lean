/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons007
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare1120 (p : Pattern) (guard : d4066 p = 1) : d98 p ≤ (0 : Int) + d499 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4066, d98, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1044 p hg
    simpa only [d4066, d98, d499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4066, d98, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1119 p hg
    simpa only [d4066, d98, d499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1121 (p : Pattern) (guard : d0 p = 1) : d99 p ≤ (0 : Int) + d425 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1122 (p : Pattern) (guard : d4066 p = 1) : d100 p ≤ (0 : Int) + d500 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4066, d100, d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1044 p hg
    simpa only [d4066, d100, d500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4066, d100, d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1121 p hg
    simpa only [d4066, d100, d500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1123 (p : Pattern) (guard : d4066 p = 1) : d101 p ≤ (0 : Int) + d501 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d101, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1120 p hg
    simpa only [d101, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d101, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1122 p hg
    simpa only [d101, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1124 (p : Pattern) (guard : d0 p = 1) : d97 p ≤ (0 : Int) + d442 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1125 (p : Pattern) (guard : d4066 p = 1) : d98 p ≤ (0 : Int) + d502 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4066, d98, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1044 p hg
    simpa only [d4066, d98, d502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4066, d98, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1124 p hg
    simpa only [d4066, d98, d502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1126 (p : Pattern) (guard : d0 p = 1) : d99 p ≤ (0 : Int) + d444 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1127 (p : Pattern) (guard : d4066 p = 1) : d100 p ≤ (0 : Int) + d503 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4066, d100, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1044 p hg
    simpa only [d4066, d100, d503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4066, d100, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1126 p hg
    simpa only [d4066, d100, d503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1128 (p : Pattern) (guard : d4066 p = 1) : d101 p ≤ (0 : Int) + d504 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d101, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1125 p hg
    simpa only [d101, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d101, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1127 p hg
    simpa only [d101, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1129 (p : Pattern) (guard : d4066 p = 1) : d101 p ≤ (0 : Int) + d505 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1123 p hg
    simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1130 (p : Pattern) (guard : d1 p = 1) : d158 p ≤ (0 : Int) + d158 p := by
  omega
theorem compare1131 (p : Pattern) (guard : d0 p = 1) : d163 p ≤ (0 : Int) + d442 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1132 (p : Pattern) (guard : d4066 p = 1) : d164 p ≤ (0 : Int) + d506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4066, d164, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d4066, d164, d506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4066, d164, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1131 p hg
    simpa only [d4066, d164, d506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1133 (p : Pattern) (guard : d0 p = 1) : d165 p ≤ (0 : Int) + d444 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1134 (p : Pattern) (guard : d4066 p = 1) : d166 p ≤ (0 : Int) + d507 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4066, d166, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d4066, d166, d507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4066, d166, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d4066, d166, d507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1135 (p : Pattern) (guard : d4066 p = 1) : d167 p ≤ (0 : Int) + d508 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d167, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d167, d508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d167, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1134 p hg
    simpa only [d167, d508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1136 (p : Pattern) (guard : d4066 p = 1) : d168 p ≤ (0 : Int) + d509 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d168, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1123 p hg
    simpa only [d168, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d168, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1135 p hg
    simpa only [d168, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1137 (p : Pattern) (guard : d4066 p = 1) : d169 p ≤ (0 : Int) + d510 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d169, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1129 p hg
    simpa only [d169, d510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d169, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1136 p hg
    simpa only [d169, d510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1138 (p : Pattern) (guard : d1 p = 1) : d223 p ≤ (0 : Int) + d223 p := by
  omega
theorem compare1139 (p : Pattern) (guard : d0 p = 1) : d224 p ≤ (0 : Int) + d463 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1140 (p : Pattern) (guard : d4066 p = 1) : d225 p ≤ (0 : Int) + d511 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4066, d225, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1138 p hg
    simpa only [d4066, d225, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4066, d225, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1139 p hg
    simpa only [d4066, d225, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1141 (p : Pattern) (guard : d1 p = 1) : d306 p ≤ (0 : Int) + d306 p := by
  omega
theorem compare1142 (p : Pattern) (guard : d0 p = 1) : d307 p ≤ (0 : Int) + d476 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1143 (p : Pattern) (guard : d4066 p = 1) : d308 p ≤ (0 : Int) + d512 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4066, d308, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1141 p hg
    simpa only [d4066, d308, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4066, d308, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1142 p hg
    simpa only [d4066, d308, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1144 (p : Pattern) (guard : d4066 p = 1) : d309 p ≤ (0 : Int) + d513 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d309, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d309, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d309, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1143 p hg
    simpa only [d309, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1145 (p : Pattern) (guard : d4066 p = 1) : d310 p ≤ (0 : Int) + d514 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d310, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1123 p hg
    simpa only [d310, d514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d310, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1144 p hg
    simpa only [d310, d514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1146 (p : Pattern) (guard : d4066 p = 1) : d311 p ≤ (0 : Int) + d515 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d311, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1129 p hg
    simpa only [d311, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d311, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1145 p hg
    simpa only [d311, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1147 (p : Pattern) (guard : d4066 p = 1) : d312 p ≤ (0 : Int) + d516 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4066 p = 1 := by simpa only [d312, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1137 p hg
    simpa only [d312, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4066 p = 1 := by simpa only [d312, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1146 p hg
    simpa only [d312, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1148 (p : Pattern) (guard : d4058 p = 1) : d169 p ≤ (0 : Int) + d169 p := by
  omega
theorem compare1149 (p : Pattern) (guard : d4058 p = 1) : d101 p ≤ (0 : Int) + d101 p := by
  omega
theorem compare1150 (p : Pattern) (guard : d0 p = 1) : d100 p ≤ (0 : Int) + d208 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1151 (p : Pattern) (guard : d4058 p = 1) : d101 p ≤ (0 : Int) + d209 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d101, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare777 p hg
    simpa only [d4058, d101, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d101, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1150 p hg
    simpa only [d4058, d101, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1152 (p : Pattern) (guard : d4058 p = 1) : d101 p ≤ (0 : Int) + d210 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1149 p hg
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1151 p hg
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1153 (p : Pattern) (guard : d0 p = 1) : d308 p ≤ (0 : Int) + d263 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1154 (p : Pattern) (guard : d4058 p = 1) : d309 p ≤ (0 : Int) + d264 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d309, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1108 p hg
    simpa only [d4058, d309, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d309, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1153 p hg
    simpa only [d4058, d309, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1155 (p : Pattern) (guard : d4058 p = 1) : d310 p ≤ (0 : Int) + d265 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d310, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1149 p hg
    simpa only [d310, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d310, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1154 p hg
    simpa only [d310, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1156 (p : Pattern) (guard : d4058 p = 1) : d311 p ≤ (0 : Int) + d266 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d311, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1152 p hg
    simpa only [d311, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d311, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1155 p hg
    simpa only [d311, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1157 (p : Pattern) (guard : d4058 p = 1) : d312 p ≤ (0 : Int) + d267 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d312, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1148 p hg
    simpa only [d312, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d312, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d312, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1158 (p : Pattern) (guard : d0 p = 1) : d88 p ≤ (0 : Int) + d87 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1159 (p : Pattern) (guard : d0 p = 1) : d96 p ≤ (0 : Int) + d87 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1160 (p : Pattern) (guard : d4068 p = 1) : d97 p ≤ (0 : Int) + d87 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1045 p hg
    simpa only [d4068, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1159 p hg
    simpa only [d4068, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1161 (p : Pattern) (guard : d4069 p = 1) : d98 p ≤ (0 : Int) + d87 p := by
  cases selected : p 116 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4069, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1158 p hg
    simpa only [d4069, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4068 p = 1 := by simpa only [d4069, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1160 p hg
    simpa only [d4069, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1162 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d87 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1163 (p : Pattern) (guard : d4068 p = 1) : d99 p ≤ (0 : Int) + d87 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1045 p hg
    simpa only [d4068, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1162 p hg
    simpa only [d4068, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1164 (p : Pattern) (guard : d4069 p = 1) : d100 p ≤ (0 : Int) + d87 p := by
  cases selected : p 116 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4069, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1158 p hg
    simpa only [d4069, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4068 p = 1 := by simpa only [d4069, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1163 p hg
    simpa only [d4069, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1165 (p : Pattern) (guard : d4069 p = 1) : d101 p ≤ (0 : Int) + d87 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4069 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1161 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4069 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1164 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1166 (p : Pattern) (guard : d0 p = 1) : d158 p ≤ (0 : Int) + d157 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1167 (p : Pattern) (guard : d1 p = 1) : d157 p ≤ (0 : Int) + d157 p := by
  omega
theorem compare1168 (p : Pattern) (guard : d0 p = 1) : d162 p ≤ (0 : Int) + d157 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1169 (p : Pattern) (guard : d4068 p = 1) : d163 p ≤ (0 : Int) + d157 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1167 p hg
    simpa only [d4068, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1168 p hg
    simpa only [d4068, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1170 (p : Pattern) (guard : d4069 p = 1) : d164 p ≤ (0 : Int) + d157 p := by
  cases selected : p 116 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4069, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1166 p hg
    simpa only [d4069, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4068 p = 1 := by simpa only [d4069, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1169 p hg
    simpa only [d4069, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1171 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d157 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1172 (p : Pattern) (guard : d4068 p = 1) : d165 p ≤ (0 : Int) + d157 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1167 p hg
    simpa only [d4068, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1171 p hg
    simpa only [d4068, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1173 (p : Pattern) (guard : d4069 p = 1) : d166 p ≤ (0 : Int) + d157 p := by
  cases selected : p 116 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4069, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1166 p hg
    simpa only [d4069, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4068 p = 1 := by simpa only [d4069, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1172 p hg
    simpa only [d4069, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1174 (p : Pattern) (guard : d4069 p = 1) : d167 p ≤ (0 : Int) + d157 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4069 p = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1170 p hg
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4069 p = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1173 p hg
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1175 (p : Pattern) (guard : d4069 p = 1) : d168 p ≤ (0 : Int) + d4070 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4069 p = 1 := by simpa only [d168, d4070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1165 p hg
    simpa only [d168, d4070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4069 p = 1 := by simpa only [d168, d4070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1174 p hg
    simpa only [d168, d4070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1176 (p : Pattern) (guard : d4069 p = 1) : d169 p ≤ (0 : Int) + d4071 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4069 p = 1 := by simpa only [d169, d4071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1165 p hg
    simpa only [d169, d4071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4069 p = 1 := by simpa only [d169, d4071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1175 p hg
    simpa only [d169, d4071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1177 (p : Pattern) (guard : d0 p = 1) : d223 p ≤ (0 : Int) + d222 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1178 (p : Pattern) (guard : d1 p = 1) : d222 p ≤ (0 : Int) + d222 p := by
  omega
theorem compare1179 (p : Pattern) (guard : d0 p = 1) : d162 p ≤ (0 : Int) + d222 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1180 (p : Pattern) (guard : d4068 p = 1) : d224 p ≤ (0 : Int) + d222 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1178 p hg
    simpa only [d4068, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1179 p hg
    simpa only [d4068, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1181 (p : Pattern) (guard : d4069 p = 1) : d225 p ≤ (0 : Int) + d222 p := by
  cases selected : p 116 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4069, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1177 p hg
    simpa only [d4069, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4068 p = 1 := by simpa only [d4069, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1180 p hg
    simpa only [d4069, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1182 (p : Pattern) (guard : d0 p = 1) : d306 p ≤ (0 : Int) + d305 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1183 (p : Pattern) (guard : d1 p = 1) : d305 p ≤ (0 : Int) + d305 p := by
  omega
theorem compare1184 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d305 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1185 (p : Pattern) (guard : d4068 p = 1) : d307 p ≤ (0 : Int) + d305 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1183 p hg
    simpa only [d4068, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1184 p hg
    simpa only [d4068, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1186 (p : Pattern) (guard : d4069 p = 1) : d308 p ≤ (0 : Int) + d305 p := by
  cases selected : p 116 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4069, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1182 p hg
    simpa only [d4069, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4068 p = 1 := by simpa only [d4069, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1185 p hg
    simpa only [d4069, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1187 (p : Pattern) (guard : d4069 p = 1) : d309 p ≤ (0 : Int) + d4072 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4069 p = 1 := by simpa only [d309, d4072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d309, d4072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4069 p = 1 := by simpa only [d309, d4072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1186 p hg
    simpa only [d309, d4072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1188 (p : Pattern) (guard : d4069 p = 1) : d310 p ≤ (0 : Int) + d4073 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4069 p = 1 := by simpa only [d310, d4073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1165 p hg
    simpa only [d310, d4073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4069 p = 1 := by simpa only [d310, d4073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1187 p hg
    simpa only [d310, d4073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1189 (p : Pattern) (guard : d4069 p = 1) : d311 p ≤ (0 : Int) + d4074 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4069 p = 1 := by simpa only [d311, d4074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1165 p hg
    simpa only [d311, d4074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4069 p = 1 := by simpa only [d311, d4074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1188 p hg
    simpa only [d311, d4074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1190 (p : Pattern) (guard : d4069 p = 1) : d312 p ≤ (0 : Int) + d4075 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4069 p = 1 := by simpa only [d312, d4075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1176 p hg
    simpa only [d312, d4075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4069 p = 1 := by simpa only [d312, d4075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1189 p hg
    simpa only [d312, d4075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1191 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare824 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1192 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d4 p := by
  change (0 : Int) ≤ (0 : Int) + 4
  decide
theorem compare1193 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d17 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1192 p hg
    simpa only [d13, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d13, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1194 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d18 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1192 p hg
    simpa only [d14, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1193 p hg
    simpa only [d14, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1195 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (0 : Int) + d19 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1194 p hg
    simpa only [d15, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d15, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1196 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d20 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1194 p hg
    simpa only [d16, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1195 p hg
    simpa only [d16, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1197 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (0 : Int) + d55 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1196 p hg
    simpa only [d21, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare983 p hg
    simpa only [d21, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1198 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1191 p hg
    simpa only [d22, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1197 p hg
    simpa only [d22, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1199 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (0 : Int) + d10 p := by
  change (4 : Int) ≤ (0 : Int) + 10
  decide
theorem compare1200 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1199 p hg
    simpa only [d17, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d17, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1201 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (0 : Int) + d58 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1199 p hg
    simpa only [d18, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1200 p hg
    simpa only [d18, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1202 (p : Pattern) (guard : d1 p = 1) : d19 p ≤ (0 : Int) + d59 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1201 p hg
    simpa only [d19, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d19, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1203 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (0 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1201 p hg
    simpa only [d20, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1202 p hg
    simpa only [d20, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1204 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (0 : Int) + d61 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1196 p hg
    simpa only [d21, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1203 p hg
    simpa only [d21, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1205 (p : Pattern) (guard : d1 p = 1) : d28 p ≤ (0 : Int) + d64 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d28, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1204 p hg
    simpa only [d28, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d28, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare831 p hg
    simpa only [d28, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1206 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (0 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d29, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1198 p hg
    simpa only [d29, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1205 p hg
    simpa only [d29, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1207 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d14 p := by
  omega
theorem compare1208 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (0 : Int) + d6 p := by
  change (2 : Int) ≤ (0 : Int) + 6
  decide
theorem compare1209 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (0 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1208 p hg
    simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d30, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1210 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d35 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1208 p hg
    simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1209 p hg
    simpa only [d31, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1211 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (0 : Int) + d36 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1210 p hg
    simpa only [d32, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d32, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1212 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (0 : Int) + d37 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d33, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d33, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d33, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1211 p hg
    simpa only [d33, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1213 (p : Pattern) (guard : d1 p = 1) : d37 p ≤ (0 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d37, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare781 p hg
    simpa only [d37, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d37, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare958 p hg
    simpa only [d37, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1214 (p : Pattern) (guard : d1 p = 1) : d38 p ≤ (0 : Int) + d67 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d38, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d38, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d38, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1213 p hg
    simpa only [d38, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1215 (p : Pattern) (guard : d1 p = 1) : d42 p ≤ (0 : Int) + d43 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d42, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1194 p hg
    simpa only [d42, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d42, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare712 p hg
    simpa only [d42, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1216 (p : Pattern) (guard : d1 p = 1) : d44 p ≤ (0 : Int) + d68 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d44, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1215 p hg
    simpa only [d44, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d44, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare929 p hg
    simpa only [d44, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1217 (p : Pattern) (guard : d1 p = 1) : d45 p ≤ (0 : Int) + d69 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d45, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1214 p hg
    simpa only [d45, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d45, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1216 p hg
    simpa only [d45, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1218 (p : Pattern) (guard : d1 p = 1) : d46 p ≤ (0 : Int) + d43 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d46, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1194 p hg
    simpa only [d46, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d46, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d46, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1219 (p : Pattern) (guard : d1 p = 1) : d43 p ≤ (0 : Int) + d70 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d43, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1201 p hg
    simpa only [d43, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d43, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d43, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1220 (p : Pattern) (guard : d1 p = 1) : d47 p ≤ (0 : Int) + d71 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d47, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d47, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d47, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1219 p hg
    simpa only [d47, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1221 (p : Pattern) (guard : d1 p = 1) : d50 p ≤ (0 : Int) + d74 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d50, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1220 p hg
    simpa only [d50, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d50, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare801 p hg
    simpa only [d50, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1222 (p : Pattern) (guard : d1 p = 1) : d51 p ≤ (0 : Int) + d75 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d51, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1217 p hg
    simpa only [d51, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d51, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1221 p hg
    simpa only [d51, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1223 (p : Pattern) (guard : d1 p = 1) : d52 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d52, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1206 p hg
    simpa only [d52, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d52, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1222 p hg
    simpa only [d52, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1224 (p : Pattern) (guard : d0 p = 1) : d76 p ≤ (0 : Int) + d76 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1225 (p : Pattern) (guard : d4077 p = 1) : d77 p ≤ (0 : Int) + d76 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1223 p hg
    simpa only [d4077, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1224 p hg
    simpa only [d4077, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1226 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (0 : Int) + d78 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d53, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1210 p hg
    simpa only [d53, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d53, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1211 p hg
    simpa only [d53, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1227 (p : Pattern) (guard : d1 p = 1) : d79 p ≤ (0 : Int) + d83 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d79, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1226 p hg
    simpa only [d79, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d79, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare959 p hg
    simpa only [d79, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1228 (p : Pattern) (guard : d1 p = 1) : d80 p ≤ (0 : Int) + d84 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d80, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1227 p hg
    simpa only [d80, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d80, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare735 p hg
    simpa only [d80, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1229 (p : Pattern) (guard : d1 p = 1) : d81 p ≤ (0 : Int) + d85 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d81, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1228 p hg
    simpa only [d81, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d81, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d81, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1230 (p : Pattern) (guard : d1 p = 1) : d82 p ≤ (0 : Int) + d86 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d82, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1206 p hg
    simpa only [d82, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d82, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1229 p hg
    simpa only [d82, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1231 (p : Pattern) (guard : d0 p = 1) : d86 p ≤ (0 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1232 (p : Pattern) (guard : d4077 p = 1) : d87 p ≤ (0 : Int) + d86 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1230 p hg
    simpa only [d4077, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1231 p hg
    simpa only [d4077, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1233 (p : Pattern) (guard : d4077 p = 1) : d88 p ≤ (0 : Int) + d4078 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d88, d4078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1225 p hg
    simpa only [d88, d4078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d88, d4078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1232 p hg
    simpa only [d88, d4078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1234 (p : Pattern) (guard : d1 p = 1) : d89 p ≤ (0 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d89, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare830 p hg
    simpa only [d89, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d89, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare734 p hg
    simpa only [d89, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1235 (p : Pattern) (guard : d1 p = 1) : d90 p ≤ (0 : Int) + d91 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d90, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1234 p hg
    simpa only [d90, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d90, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare735 p hg
    simpa only [d90, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1236 (p : Pattern) (guard : d1 p = 1) : d92 p ≤ (0 : Int) + d93 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d92, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1235 p hg
    simpa only [d92, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d92, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare763 p hg
    simpa only [d92, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1237 (p : Pattern) (guard : d1 p = 1) : d94 p ≤ (0 : Int) + d95 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d94, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1236 p hg
    simpa only [d94, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d94, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare765 p hg
    simpa only [d94, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1238 (p : Pattern) (guard : d0 p = 1) : d95 p ≤ (0 : Int) + d95 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1239 (p : Pattern) (guard : d4077 p = 1) : d96 p ≤ (0 : Int) + d95 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1237 p hg
    simpa only [d4077, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1238 p hg
    simpa only [d4077, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1240 (p : Pattern) (guard : d4077 p = 1) : d97 p ≤ (0 : Int) + d4079 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d97, d4079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1232 p hg
    simpa only [d97, d4079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d97, d4079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1239 p hg
    simpa only [d97, d4079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1241 (p : Pattern) (guard : d4077 p = 1) : d98 p ≤ (0 : Int) + d4080 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d98, d4080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1233 p hg
    simpa only [d98, d4080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d98, d4080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1240 p hg
    simpa only [d98, d4080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1242 (p : Pattern) (guard : d4077 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare1243 (p : Pattern) (guard : d4077 p = 1) : d99 p ≤ (0 : Int) + d4081 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d99, d4081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1232 p hg
    simpa only [d99, d4081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d99, d4081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1242 p hg
    simpa only [d99, d4081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1244 (p : Pattern) (guard : d4077 p = 1) : d100 p ≤ (0 : Int) + d4082 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d100, d4082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1233 p hg
    simpa only [d100, d4082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d100, d4082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1243 p hg
    simpa only [d100, d4082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1245 (p : Pattern) (guard : d4077 p = 1) : d101 p ≤ (0 : Int) + d4083 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d101, d4083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1241 p hg
    simpa only [d101, d4083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d101, d4083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1244 p hg
    simpa only [d101, d4083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1246 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (0 : Int) + d105 p := by
  omega
theorem compare1247 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d3 p := by
  change (1 : Int) ≤ (0 : Int) + 3
  decide
theorem compare1248 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (0 : Int) + d115 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1247 p hg
    simpa only [d102, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d102, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1249 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (0 : Int) + d116 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1247 p hg
    simpa only [d103, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1248 p hg
    simpa only [d103, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1250 (p : Pattern) (guard : d1 p = 1) : d104 p ≤ (0 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d104, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1249 p hg
    simpa only [d104, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d104, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d104, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1251 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (0 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d105, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1249 p hg
    simpa only [d105, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d105, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1250 p hg
    simpa only [d105, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1252 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (0 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1251 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1253 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d5 p := by
  change (1 : Int) ≤ (0 : Int) + 5
  decide
theorem compare1254 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (0 : Int) + d106 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1253 p hg
    simpa only [d102, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d102, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1255 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (0 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1253 p hg
    simpa only [d103, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1254 p hg
    simpa only [d103, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1256 (p : Pattern) (guard : d1 p = 1) : d104 p ≤ (0 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d104, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1255 p hg
    simpa only [d104, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d104, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d104, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1257 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (0 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d105, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1255 p hg
    simpa only [d105, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d105, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1256 p hg
    simpa only [d105, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1258 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (0 : Int) + d10 p := by
  change (5 : Int) ≤ (0 : Int) + 10
  decide
theorem compare1259 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1258 p hg
    simpa only [d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
