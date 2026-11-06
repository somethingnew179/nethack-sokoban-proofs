/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons024
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare3500 (p : Pattern) (guard : d829 p = 1) : d120 p ≤ (0 : Int) + d119 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare287 p hg
    simpa only [d829, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3499 p hg
    simpa only [d829, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3501 (p : Pattern) (guard : d829 p = 1) : d121 p ≤ (0 : Int) + d505 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d121, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3500 p hg
    simpa only [d121, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d121, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2120 p hg
    simpa only [d121, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3502 (p : Pattern) (guard : d829 p = 1) : d122 p ≤ (0 : Int) + d1136 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d122, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3498 p hg
    simpa only [d122, d1136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d122, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3501 p hg
    simpa only [d122, d1136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3503 (p : Pattern) (guard : d829 p = 1) : d179 p ≤ (0 : Int) + d1137 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d179, d1137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3498 p hg
    simpa only [d179, d1137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d179, d1137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3502 p hg
    simpa only [d179, d1137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3504 (p : Pattern) (guard : d829 p = 1) : d109 p ≤ (0 : Int) + d109 p := by
  omega
theorem compare3505 (p : Pattern) (guard : d0 p = 1) : d125 p ≤ (0 : Int) + d125 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3506 (p : Pattern) (guard : d829 p = 1) : d126 p ≤ (0 : Int) + d125 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare302 p hg
    simpa only [d829, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3505 p hg
    simpa only [d829, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3507 (p : Pattern) (guard : d829 p = 1) : d127 p ≤ (0 : Int) + d502 p := by
  cases selected : p 168 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d127, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3500 p hg
    simpa only [d127, d502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d127, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3506 p hg
    simpa only [d127, d502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3508 (p : Pattern) (guard : d829 p = 1) : d128 p ≤ (0 : Int) + d506 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d128, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3507 p hg
    simpa only [d128, d506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d128, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2124 p hg
    simpa only [d128, d506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3509 (p : Pattern) (guard : d829 p = 1) : d129 p ≤ (0 : Int) + d1138 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d129, d1138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3504 p hg
    simpa only [d129, d1138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d129, d1138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3508 p hg
    simpa only [d129, d1138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3510 (p : Pattern) (guard : d829 p = 1) : d237 p ≤ (0 : Int) + d1139 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d237, d1139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3504 p hg
    simpa only [d237, d1139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d237, d1139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3509 p hg
    simpa only [d237, d1139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3511 (p : Pattern) (guard : d829 p = 1) : d238 p ≤ (0 : Int) + d1140 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d238, d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3503 p hg
    simpa only [d238, d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d238, d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3510 p hg
    simpa only [d238, d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3512 (p : Pattern) (guard : d829 p = 1) : d239 p ≤ (0 : Int) + d1141 p := by
  cases selected : p 134 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d239, d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3497 p hg
    simpa only [d239, d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d239, d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3511 p hg
    simpa only [d239, d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3513 (p : Pattern) (guard : d829 p = 1) : d68 p ≤ (0 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d68, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3493 p hg
    simpa only [d68, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d68, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2120 p hg
    simpa only [d68, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3514 (p : Pattern) (guard : d829 p = 1) : d69 p ≤ (0 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d69, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3496 p hg
    simpa only [d69, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d69, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2124 p hg
    simpa only [d69, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3515 (p : Pattern) (guard : d829 p = 1) : d70 p ≤ (0 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d70, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3513 p hg
    simpa only [d70, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d70, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3514 p hg
    simpa only [d70, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3516 (p : Pattern) (guard : d829 p = 1) : d181 p ≤ (0 : Int) + d1142 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d181, d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3502 p hg
    simpa only [d181, d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d181, d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2120 p hg
    simpa only [d181, d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3517 (p : Pattern) (guard : d829 p = 1) : d240 p ≤ (0 : Int) + d1143 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d240, d1143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3509 p hg
    simpa only [d240, d1143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d240, d1143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2124 p hg
    simpa only [d240, d1143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3518 (p : Pattern) (guard : d829 p = 1) : d241 p ≤ (0 : Int) + d1144 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d241, d1144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3516 p hg
    simpa only [d241, d1144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d241, d1144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3517 p hg
    simpa only [d241, d1144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3519 (p : Pattern) (guard : d829 p = 1) : d242 p ≤ (0 : Int) + d1145 p := by
  cases selected : p 134 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d242, d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3515 p hg
    simpa only [d242, d1145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d242, d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3518 p hg
    simpa only [d242, d1145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3520 (p : Pattern) (guard : d829 p = 1) : d243 p ≤ (0 : Int) + d1146 p := by
  cases selected : p 133 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d243, d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3512 p hg
    simpa only [d243, d1146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d243, d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3519 p hg
    simpa only [d243, d1146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3521 (p : Pattern) (guard : d829 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare3522 (p : Pattern) (guard : d829 p = 1) : d244 p ≤ (0 : Int) + d1147 p := by
  cases selected : p 133 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d244, d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3519 p hg
    simpa only [d244, d1147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d244, d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3521 p hg
    simpa only [d244, d1147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3523 (p : Pattern) (guard : d829 p = 1) : d245 p ≤ (0 : Int) + d1148 p := by
  cases selected : p 132 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d245, d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3520 p hg
    simpa only [d245, d1148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d245, d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3522 p hg
    simpa only [d245, d1148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3524 (p : Pattern) (guard : d829 p = 1) : d137 p ≤ (0 : Int) + d55 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare449 p hg
    simpa only [d829, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d829, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3525 (p : Pattern) (guard : d829 p = 1) : d139 p ≤ (0 : Int) + d505 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d139, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3500 p hg
    simpa only [d139, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d139, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3524 p hg
    simpa only [d139, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3526 (p : Pattern) (guard : d829 p = 1) : d153 p ≤ (0 : Int) + d1136 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d153, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3493 p hg
    simpa only [d153, d1136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d153, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3525 p hg
    simpa only [d153, d1136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3527 (p : Pattern) (guard : d829 p = 1) : d186 p ≤ (0 : Int) + d1137 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d186, d1137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3493 p hg
    simpa only [d186, d1137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d186, d1137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3526 p hg
    simpa only [d186, d1137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3528 (p : Pattern) (guard : d829 p = 1) : d143 p ≤ (0 : Int) + d60 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare458 p hg
    simpa only [d829, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2550 p hg
    simpa only [d829, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3529 (p : Pattern) (guard : d829 p = 1) : d144 p ≤ (0 : Int) + d65 p := by
  cases selected : p 168 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d144, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3524 p hg
    simpa only [d144, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d144, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3528 p hg
    simpa only [d144, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3530 (p : Pattern) (guard : d829 p = 1) : d146 p ≤ (0 : Int) + d506 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d146, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3507 p hg
    simpa only [d146, d506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d146, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3529 p hg
    simpa only [d146, d506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3531 (p : Pattern) (guard : d829 p = 1) : d155 p ≤ (0 : Int) + d1138 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d155, d1138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3496 p hg
    simpa only [d155, d1138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d155, d1138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3530 p hg
    simpa only [d155, d1138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3532 (p : Pattern) (guard : d829 p = 1) : d246 p ≤ (0 : Int) + d1139 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d246, d1139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3496 p hg
    simpa only [d246, d1139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d246, d1139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3531 p hg
    simpa only [d246, d1139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3533 (p : Pattern) (guard : d829 p = 1) : d247 p ≤ (0 : Int) + d1140 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d247, d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3527 p hg
    simpa only [d247, d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d247, d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3532 p hg
    simpa only [d247, d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3534 (p : Pattern) (guard : d829 p = 1) : d248 p ≤ (0 : Int) + d1149 p := by
  cases selected : p 134 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d248, d1149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3533 p hg
    simpa only [d248, d1149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d248, d1149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3521 p hg
    simpa only [d248, d1149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3535 (p : Pattern) (guard : d829 p = 1) : d138 p ≤ (0 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d138, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2397 p hg
    simpa only [d138, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d138, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3524 p hg
    simpa only [d138, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3536 (p : Pattern) (guard : d829 p = 1) : d140 p ≤ (0 : Int) + d1136 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d140, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3535 p hg
    simpa only [d140, d1136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d140, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3525 p hg
    simpa only [d140, d1136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3537 (p : Pattern) (guard : d829 p = 1) : d188 p ≤ (0 : Int) + d1142 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d188, d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3536 p hg
    simpa only [d188, d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d188, d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2120 p hg
    simpa only [d188, d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3538 (p : Pattern) (guard : d829 p = 1) : d145 p ≤ (0 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d145, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2400 p hg
    simpa only [d145, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d145, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3529 p hg
    simpa only [d145, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3539 (p : Pattern) (guard : d829 p = 1) : d147 p ≤ (0 : Int) + d1138 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d147, d1138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3538 p hg
    simpa only [d147, d1138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d147, d1138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3530 p hg
    simpa only [d147, d1138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3540 (p : Pattern) (guard : d829 p = 1) : d249 p ≤ (0 : Int) + d1143 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d249, d1143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3539 p hg
    simpa only [d249, d1143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d249, d1143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2124 p hg
    simpa only [d249, d1143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3541 (p : Pattern) (guard : d829 p = 1) : d250 p ≤ (0 : Int) + d1144 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d250, d1144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3537 p hg
    simpa only [d250, d1144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d250, d1144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3540 p hg
    simpa only [d250, d1144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3542 (p : Pattern) (guard : d829 p = 1) : d251 p ≤ (0 : Int) + d1150 p := by
  cases selected : p 134 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d251, d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3541 p hg
    simpa only [d251, d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d251, d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3521 p hg
    simpa only [d251, d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3543 (p : Pattern) (guard : d829 p = 1) : d252 p ≤ (0 : Int) + d1151 p := by
  cases selected : p 133 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d252, d1151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3534 p hg
    simpa only [d252, d1151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d252, d1151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3542 p hg
    simpa only [d252, d1151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3544 (p : Pattern) (guard : d829 p = 1) : d191 p ≤ (0 : Int) + d1142 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d191, d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3526 p hg
    simpa only [d191, d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d191, d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2120 p hg
    simpa only [d191, d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3545 (p : Pattern) (guard : d829 p = 1) : d253 p ≤ (0 : Int) + d1143 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d253, d1143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3531 p hg
    simpa only [d253, d1143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d253, d1143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2124 p hg
    simpa only [d253, d1143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3546 (p : Pattern) (guard : d829 p = 1) : d254 p ≤ (0 : Int) + d1144 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d254, d1144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3544 p hg
    simpa only [d254, d1144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d254, d1144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3545 p hg
    simpa only [d254, d1144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3547 (p : Pattern) (guard : d829 p = 1) : d255 p ≤ (0 : Int) + d1150 p := by
  cases selected : p 134 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d255, d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3546 p hg
    simpa only [d255, d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d255, d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3521 p hg
    simpa only [d255, d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3548 (p : Pattern) (guard : d829 p = 1) : d256 p ≤ (0 : Int) + d1152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d256, d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3547 p hg
    simpa only [d256, d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d256, d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3521 p hg
    simpa only [d256, d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3549 (p : Pattern) (guard : d829 p = 1) : d257 p ≤ (0 : Int) + d1153 p := by
  cases selected : p 132 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d257, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3543 p hg
    simpa only [d257, d1153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d257, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3548 p hg
    simpa only [d257, d1153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3550 (p : Pattern) (guard : d829 p = 1) : d258 p ≤ (0 : Int) + d1154 p := by
  cases selected : p 108 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d258, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3523 p hg
    simpa only [d258, d1154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d258, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3549 p hg
    simpa only [d258, d1154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3551 (p : Pattern) (guard : d794 p = 1) : d179 p ≤ (0 : Int) + d107 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare477 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare490 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3552 (p : Pattern) (guard : d794 p = 1) : d237 p ≤ (0 : Int) + d110 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare481 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare493 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3553 (p : Pattern) (guard : d794 p = 1) : d238 p ≤ (0 : Int) + d336 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d238, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3551 p hg
    simpa only [d238, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d238, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3552 p hg
    simpa only [d238, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3554 (p : Pattern) (guard : d794 p = 1) : d239 p ≤ (0 : Int) + d337 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d239, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare475 p hg
    simpa only [d239, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d239, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3553 p hg
    simpa only [d239, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3555 (p : Pattern) (guard : d794 p = 1) : d181 p ≤ (0 : Int) + d211 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d181, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare490 p hg
    simpa only [d181, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d181, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare519 p hg
    simpa only [d181, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3556 (p : Pattern) (guard : d794 p = 1) : d240 p ≤ (0 : Int) + d212 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d240, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare493 p hg
    simpa only [d240, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d240, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare521 p hg
    simpa only [d240, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3557 (p : Pattern) (guard : d794 p = 1) : d241 p ≤ (0 : Int) + d213 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d241, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3555 p hg
    simpa only [d241, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d241, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3556 p hg
    simpa only [d241, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3558 (p : Pattern) (guard : d794 p = 1) : d242 p ≤ (0 : Int) + d341 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d242, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare523 p hg
    simpa only [d242, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d242, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3557 p hg
    simpa only [d242, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3559 (p : Pattern) (guard : d794 p = 1) : d243 p ≤ (0 : Int) + d342 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d243, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3554 p hg
    simpa only [d243, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d243, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3558 p hg
    simpa only [d243, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3560 (p : Pattern) (guard : d794 p = 1) : d244 p ≤ (0 : Int) + d343 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d244, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3558 p hg
    simpa only [d244, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d244, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare500 p hg
    simpa only [d244, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3561 (p : Pattern) (guard : d794 p = 1) : d245 p ≤ (0 : Int) + d344 p := by
  cases selected : p 132 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d245, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3559 p hg
    simpa only [d245, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d245, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3560 p hg
    simpa only [d245, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3562 (p : Pattern) (guard : d794 p = 1) : d186 p ≤ (0 : Int) + d114 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare473 p hg
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1642 p hg
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3563 (p : Pattern) (guard : d794 p = 1) : d246 p ≤ (0 : Int) + d116 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare474 p hg
    simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1644 p hg
    simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3564 (p : Pattern) (guard : d794 p = 1) : d247 p ≤ (0 : Int) + d335 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d247, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3562 p hg
    simpa only [d247, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d247, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3563 p hg
    simpa only [d247, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3565 (p : Pattern) (guard : d794 p = 1) : d248 p ≤ (0 : Int) + d345 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d248, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3564 p hg
    simpa only [d248, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d248, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare500 p hg
    simpa only [d248, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3566 (p : Pattern) (guard : d794 p = 1) : d188 p ≤ (0 : Int) + d347 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d188, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare504 p hg
    simpa only [d188, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d188, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare519 p hg
    simpa only [d188, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3567 (p : Pattern) (guard : d794 p = 1) : d249 p ≤ (0 : Int) + d349 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d249, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare508 p hg
    simpa only [d249, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d249, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare521 p hg
    simpa only [d249, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3568 (p : Pattern) (guard : d794 p = 1) : d250 p ≤ (0 : Int) + d350 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d250, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3566 p hg
    simpa only [d250, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d250, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3567 p hg
    simpa only [d250, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3569 (p : Pattern) (guard : d794 p = 1) : d251 p ≤ (0 : Int) + d351 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d251, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3568 p hg
    simpa only [d251, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d251, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare500 p hg
    simpa only [d251, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3570 (p : Pattern) (guard : d794 p = 1) : d252 p ≤ (0 : Int) + d352 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d252, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3565 p hg
    simpa only [d252, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d252, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3569 p hg
    simpa only [d252, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3571 (p : Pattern) (guard : d794 p = 1) : d191 p ≤ (0 : Int) + d338 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d191, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1642 p hg
    simpa only [d191, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d191, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare519 p hg
    simpa only [d191, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3572 (p : Pattern) (guard : d794 p = 1) : d253 p ≤ (0 : Int) + d339 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d253, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1644 p hg
    simpa only [d253, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d253, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare521 p hg
    simpa only [d253, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3573 (p : Pattern) (guard : d794 p = 1) : d254 p ≤ (0 : Int) + d340 p := by
  cases selected : p 141 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d254, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3571 p hg
    simpa only [d254, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d254, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3572 p hg
    simpa only [d254, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3574 (p : Pattern) (guard : d794 p = 1) : d255 p ≤ (0 : Int) + d353 p := by
  cases selected : p 134 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d255, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3573 p hg
    simpa only [d255, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d255, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare500 p hg
    simpa only [d255, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3575 (p : Pattern) (guard : d794 p = 1) : d256 p ≤ (0 : Int) + d354 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d256, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3574 p hg
    simpa only [d256, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d256, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare500 p hg
    simpa only [d256, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3576 (p : Pattern) (guard : d794 p = 1) : d257 p ≤ (0 : Int) + d355 p := by
  cases selected : p 132 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d257, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3570 p hg
    simpa only [d257, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d257, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3575 p hg
    simpa only [d257, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3577 (p : Pattern) (guard : d794 p = 1) : d258 p ≤ (0 : Int) + d356 p := by
  cases selected : p 108 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d258, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3561 p hg
    simpa only [d258, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d258, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3576 p hg
    simpa only [d258, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3578 (p : Pattern) (guard : d0 p = 1) : d122 p ≤ (0 : Int) + d107 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3579 (p : Pattern) (guard : d742 p = 1) : d179 p ≤ (0 : Int) + d108 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d179, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare324 p hg
    simpa only [d742, d179, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d179, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3578 p hg
    simpa only [d742, d179, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3580 (p : Pattern) (guard : d0 p = 1) : d129 p ≤ (0 : Int) + d110 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3581 (p : Pattern) (guard : d742 p = 1) : d237 p ≤ (0 : Int) + d111 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d237, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare327 p hg
    simpa only [d742, d237, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d237, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3580 p hg
    simpa only [d742, d237, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3582 (p : Pattern) (guard : d742 p = 1) : d238 p ≤ (0 : Int) + d112 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d238, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3579 p hg
    simpa only [d238, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d238, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3581 p hg
    simpa only [d238, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3583 (p : Pattern) (guard : d742 p = 1) : d239 p ≤ (0 : Int) + d113 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d239, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1444 p hg
    simpa only [d239, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d239, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3582 p hg
    simpa only [d239, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3584 (p : Pattern) (guard : d742 p = 1) : d243 p ≤ (0 : Int) + d134 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d243, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3583 p hg
    simpa only [d243, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d243, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1481 p hg
    simpa only [d243, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3585 (p : Pattern) (guard : d742 p = 1) : d245 p ≤ (0 : Int) + d136 p := by
  cases selected : p 132 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d245, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3584 p hg
    simpa only [d245, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d245, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1723 p hg
    simpa only [d245, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3586 (p : Pattern) (guard : d0 p = 1) : d153 p ≤ (0 : Int) + d57 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3587 (p : Pattern) (guard : d742 p = 1) : d186 p ≤ (0 : Int) + d57 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d742, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3586 p hg
    simpa only [d742, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3588 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (0 : Int) + d63 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3589 (p : Pattern) (guard : d742 p = 1) : d246 p ≤ (0 : Int) + d63 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare320 p hg
    simpa only [d742, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3588 p hg
    simpa only [d742, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3590 (p : Pattern) (guard : d742 p = 1) : d247 p ≤ (0 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d247, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3587 p hg
    simpa only [d247, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d247, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3589 p hg
    simpa only [d247, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3591 (p : Pattern) (guard : d742 p = 1) : d248 p ≤ (0 : Int) + d67 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d248, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3590 p hg
    simpa only [d248, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d248, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare346 p hg
    simpa only [d248, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3592 (p : Pattern) (guard : d742 p = 1) : d252 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d252, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3591 p hg
    simpa only [d252, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d252, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1491 p hg
    simpa only [d252, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3593 (p : Pattern) (guard : d742 p = 1) : d257 p ≤ (0 : Int) + d160 p := by
  cases selected : p 132 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d257, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3592 p hg
    simpa only [d257, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d257, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1729 p hg
    simpa only [d257, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3594 (p : Pattern) (guard : d742 p = 1) : d258 p ≤ (0 : Int) + d161 p := by
  cases selected : p 108 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d258, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3585 p hg
    simpa only [d258, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d258, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3593 p hg
    simpa only [d258, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3595 (p : Pattern) (guard : d793 p = 1) : d57 p ≤ (0 : Int) + d57 p := by
  omega
theorem compare3596 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (0 : Int) + d55 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare286 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare433 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3597 (p : Pattern) (guard : d793 p = 1) : d57 p ≤ (0 : Int) + d55 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare318 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3596 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3598 (p : Pattern) (guard : d793 p = 1) : d57 p ≤ (0 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3595 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3597 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3599 (p : Pattern) (guard : d793 p = 1) : d63 p ≤ (0 : Int) + d63 p := by
  omega
theorem compare3600 (p : Pattern) (guard : d1 p = 1) : d63 p ≤ (0 : Int) + d65 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare457 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare438 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3601 (p : Pattern) (guard : d793 p = 1) : d63 p ≤ (0 : Int) + d65 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare321 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3600 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3602 (p : Pattern) (guard : d793 p = 1) : d63 p ≤ (0 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3599 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3601 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3603 (p : Pattern) (guard : d793 p = 1) : d64 p ≤ (0 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d64, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3598 p hg
    simpa only [d64, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d64, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3602 p hg
    simpa only [d64, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3604 (p : Pattern) (guard : d793 p = 1) : d106 p ≤ (0 : Int) + d106 p := by
  omega
theorem compare3605 (p : Pattern) (guard : d1 p = 1) : d121 p ≤ (0 : Int) + d55 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare452 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3606 (p : Pattern) (guard : d793 p = 1) : d122 p ≤ (0 : Int) + d55 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d793, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare476 p hg
    simpa only [d793, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d793, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3605 p hg
    simpa only [d793, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3607 (p : Pattern) (guard : d793 p = 1) : d179 p ≤ (0 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d179, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3604 p hg
    simpa only [d179, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d179, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3606 p hg
    simpa only [d179, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3608 (p : Pattern) (guard : d793 p = 1) : d109 p ≤ (0 : Int) + d109 p := by
  omega
theorem compare3609 (p : Pattern) (guard : d1 p = 1) : d128 p ≤ (0 : Int) + d65 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare463 p hg
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare440 p hg
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3610 (p : Pattern) (guard : d793 p = 1) : d129 p ≤ (0 : Int) + d65 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d793, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare480 p hg
    simpa only [d793, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d793, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3609 p hg
    simpa only [d793, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3611 (p : Pattern) (guard : d793 p = 1) : d237 p ≤ (0 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d237, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3608 p hg
    simpa only [d237, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d237, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3610 p hg
    simpa only [d237, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3612 (p : Pattern) (guard : d793 p = 1) : d238 p ≤ (0 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d238, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3607 p hg
    simpa only [d238, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d238, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3611 p hg
    simpa only [d238, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3613 (p : Pattern) (guard : d793 p = 1) : d239 p ≤ (0 : Int) + d232 p := by
  cases selected : p 134 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d239, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3603 p hg
    simpa only [d239, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d239, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3612 p hg
    simpa only [d239, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3614 (p : Pattern) (guard : d0 p = 1) : d242 p ≤ (0 : Int) + d232 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3615 (p : Pattern) (guard : d802 p = 1) : d243 p ≤ (0 : Int) + d232 p := by
  cases selected : p 133 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d802, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3613 p hg
    simpa only [d802, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d802, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3614 p hg
    simpa only [d802, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3616 (p : Pattern) (guard : d793 p = 1) : d55 p ≤ (0 : Int) + d55 p := by
  omega
theorem compare3617 (p : Pattern) (guard : d793 p = 1) : d68 p ≤ (0 : Int) + d55 p := by
  cases selected : p 158 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3597 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3616 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3618 (p : Pattern) (guard : d793 p = 1) : d65 p ≤ (0 : Int) + d65 p := by
  omega
theorem compare3619 (p : Pattern) (guard : d793 p = 1) : d69 p ≤ (0 : Int) + d65 p := by
  cases selected : p 158 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3601 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3618 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3620 (p : Pattern) (guard : d793 p = 1) : d70 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d70, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3617 p hg
    simpa only [d70, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d70, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3619 p hg
    simpa only [d70, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3621 (p : Pattern) (guard : d793 p = 1) : d181 p ≤ (0 : Int) + d55 p := by
  cases selected : p 158 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3606 p hg
    simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3616 p hg
    simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3622 (p : Pattern) (guard : d793 p = 1) : d240 p ≤ (0 : Int) + d65 p := by
  cases selected : p 158 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3610 p hg
    simpa only [d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3618 p hg
    simpa only [d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3623 (p : Pattern) (guard : d793 p = 1) : d241 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d241, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3621 p hg
    simpa only [d241, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d241, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3622 p hg
    simpa only [d241, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3624 (p : Pattern) (guard : d793 p = 1) : d242 p ≤ (0 : Int) + d66 p := by
  cases selected : p 134 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3620 p hg
    simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3625 (p : Pattern) (guard : d802 p = 1) : d244 p ≤ (0 : Int) + d66 p := by
  cases selected : p 133 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d802, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3624 p hg
    simpa only [d802, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d802, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d802, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3626 (p : Pattern) (guard : d802 p = 1) : d245 p ≤ (0 : Int) + d1155 p := by
  cases selected : p 132 with
  | false =>
    have hg : d802 p = 1 := by simpa only [d245, d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3615 p hg
    simpa only [d245, d1155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d802 p = 1 := by simpa only [d245, d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3625 p hg
    simpa only [d245, d1155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3627 (p : Pattern) (guard : d0 p = 1) : d57 p ≤ (0 : Int) + d138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3628 (p : Pattern) (guard : d793 p = 1) : d57 p ≤ (0 : Int) + d138 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3627 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare289 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3629 (p : Pattern) (guard : d793 p = 1) : d153 p ≤ (0 : Int) + d55 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d793, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare318 p hg
    simpa only [d793, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d793, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare453 p hg
    simpa only [d793, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3630 (p : Pattern) (guard : d793 p = 1) : d186 p ≤ (0 : Int) + d803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d186, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3628 p hg
    simpa only [d186, d803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d186, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3629 p hg
    simpa only [d186, d803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3631 (p : Pattern) (guard : d0 p = 1) : d63 p ≤ (0 : Int) + d145 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3632 (p : Pattern) (guard : d793 p = 1) : d63 p ≤ (0 : Int) + d145 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3631 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare306 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3633 (p : Pattern) (guard : d793 p = 1) : d155 p ≤ (0 : Int) + d65 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d793, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare321 p hg
    simpa only [d793, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d793, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare464 p hg
    simpa only [d793, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3634 (p : Pattern) (guard : d793 p = 1) : d246 p ≤ (0 : Int) + d804 p := by
  cases selected : p 158 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d246, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3632 p hg
    simpa only [d246, d804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d246, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3633 p hg
    simpa only [d246, d804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3635 (p : Pattern) (guard : d793 p = 1) : d247 p ≤ (0 : Int) + d805 p := by
  cases selected : p 141 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d247, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3630 p hg
    simpa only [d247, d805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d247, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3634 p hg
    simpa only [d247, d805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3636 (p : Pattern) (guard : d793 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare3637 (p : Pattern) (guard : d793 p = 1) : d248 p ≤ (0 : Int) + d806 p := by
  cases selected : p 134 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d248, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3635 p hg
    simpa only [d248, d806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d248, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3636 p hg
    simpa only [d248, d806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3638 (p : Pattern) (guard : d0 p = 1) : d251 p ≤ (0 : Int) + d806 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3639 (p : Pattern) (guard : d802 p = 1) : d252 p ≤ (0 : Int) + d806 p := by
  cases selected : p 133 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d802, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3637 p hg
    simpa only [d802, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d802, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3638 p hg
    simpa only [d802, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
