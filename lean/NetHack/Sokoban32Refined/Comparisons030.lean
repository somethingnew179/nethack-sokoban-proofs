/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons029
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare4200 (p : Pattern) (guard : d985 p = 1) : d18 p ≤ (0 : Int) + d743 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d18, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3978 p hg
    simpa only [d18, d743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d18, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4199 p hg
    simpa only [d18, d743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4201 (p : Pattern) (guard : d985 p = 1) : d19 p ≤ (0 : Int) + d19 p := by
  omega
theorem compare4202 (p : Pattern) (guard : d985 p = 1) : d20 p ≤ (0 : Int) + d751 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d20, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4200 p hg
    simpa only [d20, d751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d20, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4201 p hg
    simpa only [d20, d751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4203 (p : Pattern) (guard : d985 p = 1) : d21 p ≤ (0 : Int) + d21 p := by
  omega
theorem compare4204 (p : Pattern) (guard : d985 p = 1) : d22 p ≤ (0 : Int) + d746 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d22, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3986 p hg
    simpa only [d22, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d22, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4203 p hg
    simpa only [d22, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4205 (p : Pattern) (guard : d985 p = 1) : d23 p ≤ (0 : Int) + d23 p := by
  omega
theorem compare4206 (p : Pattern) (guard : d985 p = 1) : d24 p ≤ (0 : Int) + d752 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d24, d752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4204 p hg
    simpa only [d24, d752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d24, d752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4205 p hg
    simpa only [d24, d752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4207 (p : Pattern) (guard : d985 p = 1) : d25 p ≤ (0 : Int) + d753 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d25, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4202 p hg
    simpa only [d25, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d25, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4206 p hg
    simpa only [d25, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4208 (p : Pattern) (guard : d985 p = 1) : d26 p ≤ (0 : Int) + d754 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d26, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4202 p hg
    simpa only [d26, d754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d26, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4207 p hg
    simpa only [d26, d754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4209 (p : Pattern) (guard : d985 p = 1) : d27 p ≤ (0 : Int) + d755 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d27, d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3992 p hg
    simpa only [d27, d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d27, d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4208 p hg
    simpa only [d27, d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4210 (p : Pattern) (guard : d985 p = 1) : d28 p ≤ (0 : Int) + d756 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d28, d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3992 p hg
    simpa only [d28, d756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d28, d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4209 p hg
    simpa only [d28, d756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4211 (p : Pattern) (guard : d985 p = 1) : d29 p ≤ (0 : Int) + d3 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d985, d29, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare103 p hg
    simpa only [d985, d29, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d985, d29, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3983 p hg
    simpa only [d985, d29, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4212 (p : Pattern) (guard : d985 p = 1) : d30 p ≤ (0 : Int) + d17 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4211 p hg
    simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4213 (p : Pattern) (guard : d985 p = 1) : d31 p ≤ (0 : Int) + d743 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d31, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3978 p hg
    simpa only [d31, d743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d31, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4212 p hg
    simpa only [d31, d743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4214 (p : Pattern) (guard : d985 p = 1) : d32 p ≤ (0 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4212 p hg
    simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4215 (p : Pattern) (guard : d985 p = 1) : d33 p ≤ (0 : Int) + d751 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d33, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4213 p hg
    simpa only [d33, d751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d33, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4214 p hg
    simpa only [d33, d751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4216 (p : Pattern) (guard : d985 p = 1) : d34 p ≤ (0 : Int) + d753 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d34, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4215 p hg
    simpa only [d34, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d34, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4206 p hg
    simpa only [d34, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4217 (p : Pattern) (guard : d985 p = 1) : d35 p ≤ (0 : Int) + d754 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d35, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4215 p hg
    simpa only [d35, d754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d35, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4216 p hg
    simpa only [d35, d754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4218 (p : Pattern) (guard : d985 p = 1) : d36 p ≤ (0 : Int) + d755 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d36, d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3992 p hg
    simpa only [d36, d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d36, d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4217 p hg
    simpa only [d36, d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4219 (p : Pattern) (guard : d985 p = 1) : d43 p ≤ (0 : Int) + d754 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4003 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4208 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4220 (p : Pattern) (guard : d985 p = 1) : d44 p ≤ (0 : Int) + d757 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d44, d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4218 p hg
    simpa only [d44, d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d44, d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4219 p hg
    simpa only [d44, d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4221 (p : Pattern) (guard : d985 p = 1) : d45 p ≤ (0 : Int) + d758 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d45, d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4210 p hg
    simpa only [d45, d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d45, d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4220 p hg
    simpa only [d45, d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4222 (p : Pattern) (guard : d985 p = 1) : d46 p ≤ (0 : Int) + d759 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d46, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3991 p hg
    simpa only [d46, d759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d46, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4207 p hg
    simpa only [d46, d759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4223 (p : Pattern) (guard : d985 p = 1) : d47 p ≤ (0 : Int) + d760 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d47, d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3991 p hg
    simpa only [d47, d760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d47, d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4222 p hg
    simpa only [d47, d760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4224 (p : Pattern) (guard : d985 p = 1) : d48 p ≤ (0 : Int) + d759 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d48, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3991 p hg
    simpa only [d48, d759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d48, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4216 p hg
    simpa only [d48, d759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4225 (p : Pattern) (guard : d985 p = 1) : d49 p ≤ (0 : Int) + d753 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4002 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4207 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4226 (p : Pattern) (guard : d985 p = 1) : d50 p ≤ (0 : Int) + d761 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d50, d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4224 p hg
    simpa only [d50, d761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d50, d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4225 p hg
    simpa only [d50, d761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4227 (p : Pattern) (guard : d985 p = 1) : d51 p ≤ (0 : Int) + d762 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d51, d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4223 p hg
    simpa only [d51, d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d51, d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4226 p hg
    simpa only [d51, d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4228 (p : Pattern) (guard : d985 p = 1) : d54 p ≤ (0 : Int) + d765 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d54, d765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4202 p hg
    simpa only [d54, d765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d54, d765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d54, d765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4229 (p : Pattern) (guard : d985 p = 1) : d55 p ≤ (0 : Int) + d766 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d55, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4207 p hg
    simpa only [d55, d766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d55, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4228 p hg
    simpa only [d55, d766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4230 (p : Pattern) (guard : d985 p = 1) : d56 p ≤ (0 : Int) + d767 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d56, d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4016 p hg
    simpa only [d56, d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d56, d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4229 p hg
    simpa only [d56, d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4231 (p : Pattern) (guard : d985 p = 1) : d57 p ≤ (0 : Int) + d768 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d57, d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4016 p hg
    simpa only [d57, d768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d57, d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4230 p hg
    simpa only [d57, d768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4232 (p : Pattern) (guard : d985 p = 1) : d58 p ≤ (0 : Int) + d765 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d58, d765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4215 p hg
    simpa only [d58, d765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d58, d765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d58, d765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4233 (p : Pattern) (guard : d985 p = 1) : d59 p ≤ (0 : Int) + d766 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d59, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4216 p hg
    simpa only [d59, d766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d59, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d59, d766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4234 (p : Pattern) (guard : d985 p = 1) : d60 p ≤ (0 : Int) + d767 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d60, d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4016 p hg
    simpa only [d60, d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d60, d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4233 p hg
    simpa only [d60, d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4235 (p : Pattern) (guard : d985 p = 1) : d63 p ≤ (0 : Int) + d766 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4023 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4229 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4236 (p : Pattern) (guard : d985 p = 1) : d64 p ≤ (0 : Int) + d769 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d64, d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4234 p hg
    simpa only [d64, d769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d64, d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4235 p hg
    simpa only [d64, d769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4237 (p : Pattern) (guard : d985 p = 1) : d65 p ≤ (0 : Int) + d770 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d65, d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4231 p hg
    simpa only [d65, d770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d65, d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4236 p hg
    simpa only [d65, d770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4238 (p : Pattern) (guard : d985 p = 1) : d66 p ≤ (0 : Int) + d771 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d66, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4227 p hg
    simpa only [d66, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d66, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4237 p hg
    simpa only [d66, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4239 (p : Pattern) (guard : d985 p = 1) : d67 p ≤ (0 : Int) + d772 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d67, d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4221 p hg
    simpa only [d67, d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d67, d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4238 p hg
    simpa only [d67, d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4240 (p : Pattern) (guard : d985 p = 1) : d70 p ≤ (0 : Int) + d773 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d70, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4206 p hg
    simpa only [d70, d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d70, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d70, d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4241 (p : Pattern) (guard : d985 p = 1) : d71 p ≤ (0 : Int) + d774 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d71, d774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4206 p hg
    simpa only [d71, d774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d71, d774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4240 p hg
    simpa only [d71, d774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4242 (p : Pattern) (guard : d985 p = 1) : d72 p ≤ (0 : Int) + d774 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4030 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4241 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4243 (p : Pattern) (guard : d985 p = 1) : d73 p ≤ (0 : Int) + d775 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d73, d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4209 p hg
    simpa only [d73, d775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d73, d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4242 p hg
    simpa only [d73, d775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4244 (p : Pattern) (guard : d985 p = 1) : d74 p ≤ (0 : Int) + d776 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d74, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4210 p hg
    simpa only [d74, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d74, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4243 p hg
    simpa only [d74, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4245 (p : Pattern) (guard : d985 p = 1) : d75 p ≤ (0 : Int) + d773 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4029 p hg
    simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4240 p hg
    simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4246 (p : Pattern) (guard : d985 p = 1) : d76 p ≤ (0 : Int) + d777 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d76, d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4209 p hg
    simpa only [d76, d777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d76, d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4245 p hg
    simpa only [d76, d777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4247 (p : Pattern) (guard : d985 p = 1) : d77 p ≤ (0 : Int) + d778 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d77, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4210 p hg
    simpa only [d77, d778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d77, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4246 p hg
    simpa only [d77, d778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4248 (p : Pattern) (guard : d985 p = 1) : d78 p ≤ (0 : Int) + d779 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d78, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4244 p hg
    simpa only [d78, d779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d78, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4247 p hg
    simpa only [d78, d779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4249 (p : Pattern) (guard : d985 p = 1) : d79 p ≤ (0 : Int) + d780 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d79, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4222 p hg
    simpa only [d79, d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d79, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4245 p hg
    simpa only [d79, d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4250 (p : Pattern) (guard : d985 p = 1) : d80 p ≤ (0 : Int) + d781 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d80, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4223 p hg
    simpa only [d80, d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d80, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4249 p hg
    simpa only [d80, d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4251 (p : Pattern) (guard : d985 p = 1) : d81 p ≤ (0 : Int) + d782 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d81, d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4230 p hg
    simpa only [d81, d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d81, d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4245 p hg
    simpa only [d81, d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4252 (p : Pattern) (guard : d985 p = 1) : d82 p ≤ (0 : Int) + d783 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d82, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4231 p hg
    simpa only [d82, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d82, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4251 p hg
    simpa only [d82, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4253 (p : Pattern) (guard : d985 p = 1) : d83 p ≤ (0 : Int) + d784 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d83, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4250 p hg
    simpa only [d83, d784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d83, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4252 p hg
    simpa only [d83, d784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4254 (p : Pattern) (guard : d985 p = 1) : d84 p ≤ (0 : Int) + d785 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d84, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4248 p hg
    simpa only [d84, d785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d84, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4253 p hg
    simpa only [d84, d785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4255 (p : Pattern) (guard : d985 p = 1) : d85 p ≤ (0 : Int) + d786 p := by
  cases selected : p 106 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d85, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4239 p hg
    simpa only [d85, d786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d85, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4254 p hg
    simpa only [d85, d786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4256 (p : Pattern) (guard : d985 p = 1) : d87 p ≤ (0 : Int) + d788 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d87, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4202 p hg
    simpa only [d87, d788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d87, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4228 p hg
    simpa only [d87, d788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4257 (p : Pattern) (guard : d985 p = 1) : d88 p ≤ (0 : Int) + d789 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d88, d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4047 p hg
    simpa only [d88, d789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d88, d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4256 p hg
    simpa only [d88, d789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4258 (p : Pattern) (guard : d985 p = 1) : d89 p ≤ (0 : Int) + d790 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d89, d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4047 p hg
    simpa only [d89, d790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d89, d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4257 p hg
    simpa only [d89, d790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4259 (p : Pattern) (guard : d985 p = 1) : d90 p ≤ (0 : Int) + d788 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d90, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4215 p hg
    simpa only [d90, d788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d90, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d90, d788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4260 (p : Pattern) (guard : d985 p = 1) : d91 p ≤ (0 : Int) + d789 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d91, d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4047 p hg
    simpa only [d91, d789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d91, d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4259 p hg
    simpa only [d91, d789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4261 (p : Pattern) (guard : d985 p = 1) : d93 p ≤ (0 : Int) + d788 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4053 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4256 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4262 (p : Pattern) (guard : d985 p = 1) : d94 p ≤ (0 : Int) + d791 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d94, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4260 p hg
    simpa only [d94, d791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d94, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4261 p hg
    simpa only [d94, d791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4263 (p : Pattern) (guard : d985 p = 1) : d95 p ≤ (0 : Int) + d792 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d95, d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4258 p hg
    simpa only [d95, d792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d95, d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4262 p hg
    simpa only [d95, d792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4264 (p : Pattern) (guard : d985 p = 1) : d96 p ≤ (0 : Int) + d793 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d96, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4221 p hg
    simpa only [d96, d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d96, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4263 p hg
    simpa only [d96, d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4265 (p : Pattern) (guard : d985 p = 1) : d99 p ≤ (0 : Int) + d796 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d99, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4059 p hg
    simpa only [d99, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d99, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4241 p hg
    simpa only [d99, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4266 (p : Pattern) (guard : d985 p = 1) : d100 p ≤ (0 : Int) + d797 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d100, d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4059 p hg
    simpa only [d100, d797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d100, d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4265 p hg
    simpa only [d100, d797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4267 (p : Pattern) (guard : d985 p = 1) : d101 p ≤ (0 : Int) + d798 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d101, d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4265 p hg
    simpa only [d101, d798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d101, d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4242 p hg
    simpa only [d101, d798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4268 (p : Pattern) (guard : d985 p = 1) : d102 p ≤ (0 : Int) + d799 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d102, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4266 p hg
    simpa only [d102, d799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d102, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4267 p hg
    simpa only [d102, d799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4269 (p : Pattern) (guard : d985 p = 1) : d103 p ≤ (0 : Int) + d800 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d103, d800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4264 p hg
    simpa only [d103, d800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d103, d800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4268 p hg
    simpa only [d103, d800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4270 (p : Pattern) (guard : d985 p = 1) : d104 p ≤ (0 : Int) + d801 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d104, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4257 p hg
    simpa only [d104, d801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d104, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4245 p hg
    simpa only [d104, d801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4271 (p : Pattern) (guard : d985 p = 1) : d105 p ≤ (0 : Int) + d802 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d105, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4258 p hg
    simpa only [d105, d802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d105, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4270 p hg
    simpa only [d105, d802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4272 (p : Pattern) (guard : d985 p = 1) : d106 p ≤ (0 : Int) + d803 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d106, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4247 p hg
    simpa only [d106, d803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d106, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4271 p hg
    simpa only [d106, d803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4273 (p : Pattern) (guard : d985 p = 1) : d107 p ≤ (0 : Int) + d804 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d107, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4265 p hg
    simpa only [d107, d804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d107, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d107, d804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4274 (p : Pattern) (guard : d985 p = 1) : d108 p ≤ (0 : Int) + d805 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d108, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4266 p hg
    simpa only [d108, d805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d108, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4273 p hg
    simpa only [d108, d805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4275 (p : Pattern) (guard : d985 p = 1) : d109 p ≤ (0 : Int) + d806 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d109, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4058 p hg
    simpa only [d109, d806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d109, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4240 p hg
    simpa only [d109, d806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4276 (p : Pattern) (guard : d985 p = 1) : d110 p ≤ (0 : Int) + d807 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d110, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4058 p hg
    simpa only [d110, d807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d110, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4275 p hg
    simpa only [d110, d807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4277 (p : Pattern) (guard : d985 p = 1) : d111 p ≤ (0 : Int) + d808 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d111, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4275 p hg
    simpa only [d111, d808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d111, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d111, d808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4278 (p : Pattern) (guard : d985 p = 1) : d112 p ≤ (0 : Int) + d809 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d112, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4276 p hg
    simpa only [d112, d809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d112, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4277 p hg
    simpa only [d112, d809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4279 (p : Pattern) (guard : d985 p = 1) : d113 p ≤ (0 : Int) + d810 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d113, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4274 p hg
    simpa only [d113, d810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d113, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4278 p hg
    simpa only [d113, d810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4280 (p : Pattern) (guard : d985 p = 1) : d114 p ≤ (0 : Int) + d811 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d114, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4272 p hg
    simpa only [d114, d811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d114, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4279 p hg
    simpa only [d114, d811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4281 (p : Pattern) (guard : d985 p = 1) : d115 p ≤ (0 : Int) + d812 p := by
  cases selected : p 106 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d115, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4269 p hg
    simpa only [d115, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d115, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4280 p hg
    simpa only [d115, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4282 (p : Pattern) (guard : d985 p = 1) : d116 p ≤ (0 : Int) + d813 p := by
  cases selected : p 86 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d116, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4255 p hg
    simpa only [d116, d813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d116, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4281 p hg
    simpa only [d116, d813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4283 (p : Pattern) (guard : d985 p = 1) : d117 p ≤ (0 : Int) + d814 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d117, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4247 p hg
    simpa only [d117, d814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d117, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4253 p hg
    simpa only [d117, d814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4284 (p : Pattern) (guard : d985 p = 1) : d118 p ≤ (0 : Int) + d815 p := by
  cases selected : p 106 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d118, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4239 p hg
    simpa only [d118, d815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d118, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4283 p hg
    simpa only [d118, d815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4285 (p : Pattern) (guard : d985 p = 1) : d119 p ≤ (0 : Int) + d751 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4215 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4202 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4286 (p : Pattern) (guard : d985 p = 1) : d120 p ≤ (0 : Int) + d788 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d120, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4285 p hg
    simpa only [d120, d788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d120, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d120, d788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4287 (p : Pattern) (guard : d985 p = 1) : d121 p ≤ (0 : Int) + d789 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d121, d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4047 p hg
    simpa only [d121, d789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d121, d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4286 p hg
    simpa only [d121, d789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4288 (p : Pattern) (guard : d985 p = 1) : d122 p ≤ (0 : Int) + d791 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d122, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4287 p hg
    simpa only [d122, d791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d122, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4261 p hg
    simpa only [d122, d791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4289 (p : Pattern) (guard : d985 p = 1) : d123 p ≤ (0 : Int) + d792 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d123, d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4258 p hg
    simpa only [d123, d792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d123, d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4288 p hg
    simpa only [d123, d792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4290 (p : Pattern) (guard : d985 p = 1) : d124 p ≤ (0 : Int) + d793 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d124, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4221 p hg
    simpa only [d124, d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d124, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4289 p hg
    simpa only [d124, d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4291 (p : Pattern) (guard : d985 p = 1) : d125 p ≤ (0 : Int) + d816 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d125, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4275 p hg
    simpa only [d125, d816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d125, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4245 p hg
    simpa only [d125, d816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4292 (p : Pattern) (guard : d985 p = 1) : d126 p ≤ (0 : Int) + d817 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d126, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4276 p hg
    simpa only [d126, d817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d126, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4291 p hg
    simpa only [d126, d817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4293 (p : Pattern) (guard : d985 p = 1) : d127 p ≤ (0 : Int) + d818 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d127, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4268 p hg
    simpa only [d127, d818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d127, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4292 p hg
    simpa only [d127, d818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4294 (p : Pattern) (guard : d985 p = 1) : d128 p ≤ (0 : Int) + d819 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d128, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4290 p hg
    simpa only [d128, d819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d128, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4293 p hg
    simpa only [d128, d819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4295 (p : Pattern) (guard : d985 p = 1) : d129 p ≤ (0 : Int) + d820 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d129, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4247 p hg
    simpa only [d129, d820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d129, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4252 p hg
    simpa only [d129, d820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4296 (p : Pattern) (guard : d985 p = 1) : d130 p ≤ (0 : Int) + d821 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d130, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4278 p hg
    simpa only [d130, d821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d130, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d130, d821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4297 (p : Pattern) (guard : d985 p = 1) : d131 p ≤ (0 : Int) + d822 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d131, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4295 p hg
    simpa only [d131, d822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d131, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4296 p hg
    simpa only [d131, d822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4298 (p : Pattern) (guard : d985 p = 1) : d132 p ≤ (0 : Int) + d823 p := by
  cases selected : p 106 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d132, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4294 p hg
    simpa only [d132, d823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d132, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4297 p hg
    simpa only [d132, d823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4299 (p : Pattern) (guard : d985 p = 1) : d133 p ≤ (0 : Int) + d824 p := by
  cases selected : p 86 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d133, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4284 p hg
    simpa only [d133, d824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d133, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4298 p hg
    simpa only [d133, d824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4300 (p : Pattern) (guard : d985 p = 1) : d134 p ≤ (0 : Int) + d825 p := by
  cases selected : p 80 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d134, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4282 p hg
    simpa only [d134, d825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d134, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4299 p hg
    simpa only [d134, d825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4301 (p : Pattern) (guard : d1 p = 1) : d134 p ≤ (2 : Int) + d134 p := by
  omega
theorem compare4302 (p : Pattern) (guard : d914 p = 1) : d16 p ≤ (2 : Int) + d16 p := by
  omega
theorem compare4303 (p : Pattern) (guard : d0 p = 1) : d27 p ≤ (2 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4304 (p : Pattern) (guard : d1175 p = 1) : d28 p ≤ (2 : Int) + d16 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4302 p hg
    simpa only [d1175, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4303 p hg
    simpa only [d1175, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4305 (p : Pattern) (guard : d0 p = 1) : d16 p ≤ (2 : Int) + d42 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4306 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (2 : Int) + d4 p := by
  omega
theorem compare4307 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (2 : Int) + d0 p := by
  omega
theorem compare4308 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (2 : Int) + d0 p := by
  change (1 : Int) ≤ (2 : Int) + 0
  decide
theorem compare4309 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (2 : Int) + d0 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4307 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4308 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4310 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (2 : Int) + d2 p := by
  omega
theorem compare4311 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (2 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4309 p hg
    simpa only [d30, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d30, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4312 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (2 : Int) + d6 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4306 p hg
    simpa only [d31, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4311 p hg
    simpa only [d31, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4313 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (2 : Int) + d37 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4311 p hg
    simpa only [d32, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d32, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4314 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (2 : Int) + d38 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d33, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4312 p hg
    simpa only [d33, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d33, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4313 p hg
    simpa only [d33, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4315 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (2 : Int) + d10 p := by
  omega
theorem compare4316 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (2 : Int) + d1 p := by
  omega
theorem compare4317 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (2 : Int) + d1 p := by
  change (2 : Int) ≤ (2 : Int) + 1
  decide
theorem compare4318 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (2 : Int) + d1 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4316 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4317 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4319 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (2 : Int) + d11 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4318 p hg
    simpa only [d21, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d21, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4320 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (2 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4315 p hg
    simpa only [d22, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4319 p hg
    simpa only [d22, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4321 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (2 : Int) + d39 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4319 p hg
    simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4322 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (2 : Int) + d40 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d24, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4320 p hg
    simpa only [d24, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d24, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4321 p hg
    simpa only [d24, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4323 (p : Pattern) (guard : d1 p = 1) : d34 p ≤ (2 : Int) + d41 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4314 p hg
    simpa only [d34, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4322 p hg
    simpa only [d34, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4324 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (2 : Int) + d42 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d35, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4314 p hg
    simpa only [d35, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d35, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4323 p hg
    simpa only [d35, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4325 (p : Pattern) (guard : d914 p = 1) : d36 p ≤ (2 : Int) + d42 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d914, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4305 p hg
    simpa only [d914, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d914, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4324 p hg
    simpa only [d914, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4326 (p : Pattern) (guard : d0 p = 1) : d43 p ≤ (2 : Int) + d42 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4327 (p : Pattern) (guard : d1175 p = 1) : d44 p ≤ (2 : Int) + d42 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4325 p hg
    simpa only [d1175, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4326 p hg
    simpa only [d1175, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4328 (p : Pattern) (guard : d1175 p = 1) : d45 p ≤ (2 : Int) + d1255 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d45, d1255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4304 p hg
    simpa only [d45, d1255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d45, d1255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4327 p hg
    simpa only [d45, d1255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4329 (p : Pattern) (guard : d914 p = 1) : d15 p ≤ (2 : Int) + d15 p := by
  omega
theorem compare4330 (p : Pattern) (guard : d0 p = 1) : d46 p ≤ (2 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4331 (p : Pattern) (guard : d1175 p = 1) : d47 p ≤ (2 : Int) + d15 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4329 p hg
    simpa only [d1175, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4330 p hg
    simpa only [d1175, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4332 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (2 : Int) + d41 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4333 (p : Pattern) (guard : d914 p = 1) : d48 p ≤ (2 : Int) + d41 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d914, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4332 p hg
    simpa only [d914, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d914, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4323 p hg
    simpa only [d914, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4334 (p : Pattern) (guard : d0 p = 1) : d49 p ≤ (2 : Int) + d41 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4335 (p : Pattern) (guard : d1175 p = 1) : d50 p ≤ (2 : Int) + d41 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4333 p hg
    simpa only [d1175, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4334 p hg
    simpa only [d1175, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4336 (p : Pattern) (guard : d1175 p = 1) : d51 p ≤ (2 : Int) + d1256 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d51, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4331 p hg
    simpa only [d51, d1256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d51, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4335 p hg
    simpa only [d51, d1256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4337 (p : Pattern) (guard : d914 p = 1) : d53 p ≤ (2 : Int) + d53 p := by
  omega
theorem compare4338 (p : Pattern) (guard : d0 p = 1) : d56 p ≤ (2 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4339 (p : Pattern) (guard : d1175 p = 1) : d57 p ≤ (2 : Int) + d53 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4337 p hg
    simpa only [d1175, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4338 p hg
    simpa only [d1175, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
