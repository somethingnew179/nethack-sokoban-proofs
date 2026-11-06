/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons079
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare11200 (p : Pattern) (guard : d4303 p = 1) : d1498 p ≤ (0 : Int) + d704 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1498, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11198 p hg
    simpa only [d1498, d704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1498, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3703 p hg
    simpa only [d1498, d704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11201 (p : Pattern) (guard : d4303 p = 1) : d1499 p ≤ (0 : Int) + d705 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1499, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11199 p hg
    simpa only [d1499, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1499, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11200 p hg
    simpa only [d1499, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11202 (p : Pattern) (guard : d4303 p = 1) : d1500 p ≤ (0 : Int) + d706 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1500, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11185 p hg
    simpa only [d1500, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1500, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11201 p hg
    simpa only [d1500, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11203 (p : Pattern) (guard : d4303 p = 1) : d1501 p ≤ (0 : Int) + d707 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1501, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11119 p hg
    simpa only [d1501, d707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1501, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11202 p hg
    simpa only [d1501, d707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11204 (p : Pattern) (guard : d4303 p = 1) : d1502 p ≤ (0 : Int) + d708 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1502, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11176 p hg
    simpa only [d1502, d708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1502, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11203 p hg
    simpa only [d1502, d708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11205 (p : Pattern) (guard : d4303 p = 1) : d1503 p ≤ (0 : Int) + d709 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4303 p = 1 := by simpa only [d1503, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11167 p hg
    simpa only [d1503, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4303 p = 1 := by simpa only [d1503, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11204 p hg
    simpa only [d1503, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11206 (p : Pattern) (guard : d4902 p = 1) : d267 p ≤ (0 : Int) + d267 p := by
  omega
theorem compare11207 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11208 (p : Pattern) (guard : d4206 p = 1) : d16 p ≤ (0 : Int) + d15 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2908 p hg
    simpa only [d4206, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11207 p hg
    simpa only [d4206, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11209 (p : Pattern) (guard : d0 p = 1) : d19 p ≤ (0 : Int) + d19 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11210 (p : Pattern) (guard : d4206 p = 1) : d20 p ≤ (0 : Int) + d19 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2916 p hg
    simpa only [d4206, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11209 p hg
    simpa only [d4206, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11211 (p : Pattern) (guard : d4206 p = 1) : d21 p ≤ (0 : Int) + d4209 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d21, d4209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11208 p hg
    simpa only [d21, d4209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d21, d4209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11210 p hg
    simpa only [d21, d4209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11212 (p : Pattern) (guard : d4206 p = 1) : d22 p ≤ (0 : Int) + d4210 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d22, d4210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11208 p hg
    simpa only [d22, d4210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d22, d4210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11211 p hg
    simpa only [d22, d4210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11213 (p : Pattern) (guard : d0 p = 1) : d25 p ≤ (0 : Int) + d25 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11214 (p : Pattern) (guard : d4206 p = 1) : d26 p ≤ (0 : Int) + d25 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2924 p hg
    simpa only [d4206, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11213 p hg
    simpa only [d4206, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11215 (p : Pattern) (guard : d4206 p = 1) : d27 p ≤ (0 : Int) + d4211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d27, d4211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11214 p hg
    simpa only [d27, d4211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d27, d4211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d27, d4211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11216 (p : Pattern) (guard : d4206 p = 1) : d28 p ≤ (0 : Int) + d4212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d28, d4212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11211 p hg
    simpa only [d28, d4212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d28, d4212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11215 p hg
    simpa only [d28, d4212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11217 (p : Pattern) (guard : d4206 p = 1) : d29 p ≤ (0 : Int) + d4213 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d29, d4213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11212 p hg
    simpa only [d29, d4213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d29, d4213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11216 p hg
    simpa only [d29, d4213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11218 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d32 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare781 p hg
    simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11219 (p : Pattern) (guard : d0 p = 1) : d32 p ≤ (0 : Int) + d32 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11220 (p : Pattern) (guard : d4206 p = 1) : d33 p ≤ (0 : Int) + d32 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11218 p hg
    simpa only [d4206, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11219 p hg
    simpa only [d4206, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11221 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d36 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1489 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11222 (p : Pattern) (guard : d0 p = 1) : d36 p ≤ (0 : Int) + d36 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11223 (p : Pattern) (guard : d4206 p = 1) : d37 p ≤ (0 : Int) + d36 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11221 p hg
    simpa only [d4206, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11222 p hg
    simpa only [d4206, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11224 (p : Pattern) (guard : d4206 p = 1) : d38 p ≤ (0 : Int) + d4255 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d38, d4255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11220 p hg
    simpa only [d38, d4255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d38, d4255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11223 p hg
    simpa only [d38, d4255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11225 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1494 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11226 (p : Pattern) (guard : d0 p = 1) : d41 p ≤ (0 : Int) + d41 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11227 (p : Pattern) (guard : d4206 p = 1) : d42 p ≤ (0 : Int) + d41 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11225 p hg
    simpa only [d4206, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11226 p hg
    simpa only [d4206, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11228 (p : Pattern) (guard : d4206 p = 1) : d43 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare901 p hg
    simpa only [d4206, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4206, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11229 (p : Pattern) (guard : d4206 p = 1) : d44 p ≤ (0 : Int) + d4218 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d44, d4218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11227 p hg
    simpa only [d44, d4218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d44, d4218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11228 p hg
    simpa only [d44, d4218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11230 (p : Pattern) (guard : d4206 p = 1) : d45 p ≤ (0 : Int) + d4257 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d45, d4257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11224 p hg
    simpa only [d45, d4257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d45, d4257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11229 p hg
    simpa only [d45, d4257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11231 (p : Pattern) (guard : d4206 p = 1) : d46 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d4206, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4206, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11232 (p : Pattern) (guard : d4206 p = 1) : d47 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11231 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11228 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11233 (p : Pattern) (guard : d4206 p = 1) : d48 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare868 p hg
    simpa only [d4206, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4206, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11234 (p : Pattern) (guard : d4206 p = 1) : d49 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11233 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11235 (p : Pattern) (guard : d4206 p = 1) : d50 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11232 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11234 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11236 (p : Pattern) (guard : d4206 p = 1) : d51 p ≤ (0 : Int) + d4903 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d51, d4903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11230 p hg
    simpa only [d51, d4903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d51, d4903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11235 p hg
    simpa only [d51, d4903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11237 (p : Pattern) (guard : d4206 p = 1) : d52 p ≤ (0 : Int) + d4904 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d52, d4904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11217 p hg
    simpa only [d52, d4904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d52, d4904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11236 p hg
    simpa only [d52, d4904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11238 (p : Pattern) (guard : d4206 p = 1) : d53 p ≤ (0 : Int) + d32 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2933 p hg
    simpa only [d4206, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11219 p hg
    simpa only [d4206, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11239 (p : Pattern) (guard : d4206 p = 1) : d54 p ≤ (0 : Int) + d4214 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d54, d4214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11208 p hg
    simpa only [d54, d4214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d54, d4214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11238 p hg
    simpa only [d54, d4214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11240 (p : Pattern) (guard : d4206 p = 1) : d55 p ≤ (0 : Int) + d4215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d55, d4215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11210 p hg
    simpa only [d55, d4215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d55, d4215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11214 p hg
    simpa only [d55, d4215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11241 (p : Pattern) (guard : d4206 p = 1) : d56 p ≤ (0 : Int) + d4216 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d56, d4216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11239 p hg
    simpa only [d56, d4216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d56, d4216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11240 p hg
    simpa only [d56, d4216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11242 (p : Pattern) (guard : d0 p = 1) : d59 p ≤ (0 : Int) + d59 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11243 (p : Pattern) (guard : d4206 p = 1) : d60 p ≤ (0 : Int) + d59 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2939 p hg
    simpa only [d4206, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11242 p hg
    simpa only [d4206, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11244 (p : Pattern) (guard : d4206 p = 1) : d61 p ≤ (0 : Int) + d4217 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d61, d4217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11210 p hg
    simpa only [d61, d4217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d61, d4217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11243 p hg
    simpa only [d61, d4217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11245 (p : Pattern) (guard : d4206 p = 1) : d62 p ≤ (0 : Int) + d41 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2943 p hg
    simpa only [d4206, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11226 p hg
    simpa only [d4206, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11246 (p : Pattern) (guard : d4206 p = 1) : d63 p ≤ (0 : Int) + d4218 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d63, d4218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11245 p hg
    simpa only [d63, d4218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d63, d4218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d63, d4218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11247 (p : Pattern) (guard : d4206 p = 1) : d64 p ≤ (0 : Int) + d4219 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d64, d4219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11244 p hg
    simpa only [d64, d4219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d64, d4219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11246 p hg
    simpa only [d64, d4219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11248 (p : Pattern) (guard : d4206 p = 1) : d65 p ≤ (0 : Int) + d4220 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d65, d4220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11241 p hg
    simpa only [d65, d4220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d65, d4220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11247 p hg
    simpa only [d65, d4220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11249 (p : Pattern) (guard : d4206 p = 1) : d66 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1508 p hg
    simpa only [d4206, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4206, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11250 (p : Pattern) (guard : d4206 p = 1) : d67 p ≤ (0 : Int) + d4261 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d67, d4261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11223 p hg
    simpa only [d67, d4261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d67, d4261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11249 p hg
    simpa only [d67, d4261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11251 (p : Pattern) (guard : d4206 p = 1) : d68 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11228 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11233 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11252 (p : Pattern) (guard : d4206 p = 1) : d69 p ≤ (0 : Int) + d4262 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d69, d4262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11250 p hg
    simpa only [d69, d4262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d69, d4262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11251 p hg
    simpa only [d69, d4262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11253 (p : Pattern) (guard : d4206 p = 1) : d70 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare815 p hg
    simpa only [d4206, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4206, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11254 (p : Pattern) (guard : d4206 p = 1) : d71 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11228 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11253 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11255 (p : Pattern) (guard : d4206 p = 1) : d72 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare711 p hg
    simpa only [d4206, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4206, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11256 (p : Pattern) (guard : d4206 p = 1) : d73 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11255 p hg
    simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11257 (p : Pattern) (guard : d4206 p = 1) : d74 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11254 p hg
    simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11256 p hg
    simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11258 (p : Pattern) (guard : d4206 p = 1) : d75 p ≤ (0 : Int) + d4905 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d75, d4905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11252 p hg
    simpa only [d75, d4905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d75, d4905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11257 p hg
    simpa only [d75, d4905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11259 (p : Pattern) (guard : d4206 p = 1) : d76 p ≤ (0 : Int) + d4906 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d76, d4906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11248 p hg
    simpa only [d76, d4906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d76, d4906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11258 p hg
    simpa only [d76, d4906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11260 (p : Pattern) (guard : d4206 p = 1) : d77 p ≤ (0 : Int) + d4907 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d77, d4907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11237 p hg
    simpa only [d77, d4907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d77, d4907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11259 p hg
    simpa only [d77, d4907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11261 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (0 : Int) + d36 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3072 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare957 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11262 (p : Pattern) (guard : d4206 p = 1) : d78 p ≤ (0 : Int) + d36 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11261 p hg
    simpa only [d4206, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11222 p hg
    simpa only [d4206, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11263 (p : Pattern) (guard : d4206 p = 1) : d79 p ≤ (0 : Int) + d4255 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d79, d4255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11238 p hg
    simpa only [d79, d4255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d79, d4255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11262 p hg
    simpa only [d79, d4255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11264 (p : Pattern) (guard : d4206 p = 1) : d80 p ≤ (0 : Int) + d4257 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d80, d4257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11263 p hg
    simpa only [d80, d4257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d80, d4257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11246 p hg
    simpa only [d80, d4257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11265 (p : Pattern) (guard : d4206 p = 1) : d81 p ≤ (0 : Int) + d4903 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d81, d4903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11264 p hg
    simpa only [d81, d4903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d81, d4903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d81, d4903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11266 (p : Pattern) (guard : d4206 p = 1) : d82 p ≤ (0 : Int) + d4904 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d82, d4904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11217 p hg
    simpa only [d82, d4904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d82, d4904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11265 p hg
    simpa only [d82, d4904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11267 (p : Pattern) (guard : d4206 p = 1) : d83 p ≤ (0 : Int) + d4261 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d83, d4261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11262 p hg
    simpa only [d83, d4261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d83, d4261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d83, d4261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11268 (p : Pattern) (guard : d4206 p = 1) : d84 p ≤ (0 : Int) + d4262 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d84, d4262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11267 p hg
    simpa only [d84, d4262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d84, d4262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d84, d4262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11269 (p : Pattern) (guard : d4206 p = 1) : d85 p ≤ (0 : Int) + d4905 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d85, d4905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11268 p hg
    simpa only [d85, d4905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d85, d4905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d85, d4905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11270 (p : Pattern) (guard : d4206 p = 1) : d86 p ≤ (0 : Int) + d4906 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d86, d4906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11248 p hg
    simpa only [d86, d4906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d86, d4906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11269 p hg
    simpa only [d86, d4906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11271 (p : Pattern) (guard : d4206 p = 1) : d87 p ≤ (0 : Int) + d4907 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d87, d4907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11266 p hg
    simpa only [d87, d4907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d87, d4907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11270 p hg
    simpa only [d87, d4907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11272 (p : Pattern) (guard : d4206 p = 1) : d88 p ≤ (0 : Int) + d4907 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11260 p hg
    simpa only [d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11271 p hg
    simpa only [d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11273 (p : Pattern) (guard : d4206 p = 1) : d89 p ≤ (0 : Int) + d4222 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d89, d4222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11214 p hg
    simpa only [d89, d4222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d89, d4222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11245 p hg
    simpa only [d89, d4222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11274 (p : Pattern) (guard : d4206 p = 1) : d90 p ≤ (0 : Int) + d4223 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d90, d4223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11273 p hg
    simpa only [d90, d4223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d90, d4223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11246 p hg
    simpa only [d90, d4223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11275 (p : Pattern) (guard : d4206 p = 1) : d91 p ≤ (0 : Int) + d4224 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d91, d4224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11246 p hg
    simpa only [d91, d4224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d91, d4224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d91, d4224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11276 (p : Pattern) (guard : d4206 p = 1) : d92 p ≤ (0 : Int) + d4225 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d92, d4225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11274 p hg
    simpa only [d92, d4225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d92, d4225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11275 p hg
    simpa only [d92, d4225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11277 (p : Pattern) (guard : d4206 p = 1) : d93 p ≤ (0 : Int) + d4226 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d93, d4226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11275 p hg
    simpa only [d93, d4226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d93, d4226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d93, d4226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11278 (p : Pattern) (guard : d4206 p = 1) : d94 p ≤ (0 : Int) + d4908 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d94, d4908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11276 p hg
    simpa only [d94, d4908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d94, d4908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11277 p hg
    simpa only [d94, d4908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11279 (p : Pattern) (guard : d4206 p = 1) : d95 p ≤ (0 : Int) + d4909 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d95, d4909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11277 p hg
    simpa only [d95, d4909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d95, d4909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d95, d4909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11280 (p : Pattern) (guard : d4206 p = 1) : d96 p ≤ (0 : Int) + d4910 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d96, d4910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11278 p hg
    simpa only [d96, d4910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d96, d4910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11279 p hg
    simpa only [d96, d4910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11281 (p : Pattern) (guard : d4206 p = 1) : d97 p ≤ (0 : Int) + d4911 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d97, d4911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11271 p hg
    simpa only [d97, d4911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d97, d4911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11280 p hg
    simpa only [d97, d4911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11282 (p : Pattern) (guard : d4206 p = 1) : d98 p ≤ (0 : Int) + d4912 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d98, d4912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11272 p hg
    simpa only [d98, d4912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d98, d4912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11281 p hg
    simpa only [d98, d4912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11283 (p : Pattern) (guard : d4206 p = 1) : d99 p ≤ (0 : Int) + d4913 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d99, d4913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11271 p hg
    simpa only [d99, d4913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d99, d4913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d99, d4913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11284 (p : Pattern) (guard : d4206 p = 1) : d100 p ≤ (0 : Int) + d4914 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d100, d4914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11272 p hg
    simpa only [d100, d4914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d100, d4914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11283 p hg
    simpa only [d100, d4914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11285 (p : Pattern) (guard : d4206 p = 1) : d101 p ≤ (0 : Int) + d4915 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d101, d4915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11282 p hg
    simpa only [d101, d4915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d101, d4915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11284 p hg
    simpa only [d101, d4915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11286 (p : Pattern) (guard : d0 p = 1) : d104 p ≤ (0 : Int) + d104 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11287 (p : Pattern) (guard : d4206 p = 1) : d105 p ≤ (0 : Int) + d104 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3002 p hg
    simpa only [d4206, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11286 p hg
    simpa only [d4206, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11288 (p : Pattern) (guard : d0 p = 1) : d108 p ≤ (0 : Int) + d108 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11289 (p : Pattern) (guard : d4206 p = 1) : d109 p ≤ (0 : Int) + d108 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3010 p hg
    simpa only [d4206, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11288 p hg
    simpa only [d4206, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11290 (p : Pattern) (guard : d4206 p = 1) : d110 p ≤ (0 : Int) + d4233 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d110, d4233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11287 p hg
    simpa only [d110, d4233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d110, d4233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11289 p hg
    simpa only [d110, d4233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11291 (p : Pattern) (guard : d4206 p = 1) : d111 p ≤ (0 : Int) + d4234 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d111, d4234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11287 p hg
    simpa only [d111, d4234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d111, d4234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11290 p hg
    simpa only [d111, d4234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11292 (p : Pattern) (guard : d4206 p = 1) : d112 p ≤ (0 : Int) + d4235 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d112, d4235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11243 p hg
    simpa only [d112, d4235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d112, d4235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d112, d4235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11293 (p : Pattern) (guard : d4206 p = 1) : d113 p ≤ (0 : Int) + d4236 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d113, d4236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11290 p hg
    simpa only [d113, d4236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d113, d4236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11292 p hg
    simpa only [d113, d4236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11294 (p : Pattern) (guard : d4206 p = 1) : d114 p ≤ (0 : Int) + d4237 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d114, d4237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11291 p hg
    simpa only [d114, d4237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d114, d4237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11293 p hg
    simpa only [d114, d4237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11295 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (0 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1249 p hg
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1563 p hg
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11296 (p : Pattern) (guard : d0 p = 1) : d117 p ≤ (0 : Int) + d117 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11297 (p : Pattern) (guard : d4206 p = 1) : d118 p ≤ (0 : Int) + d117 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11295 p hg
    simpa only [d4206, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11296 p hg
    simpa only [d4206, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11298 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (0 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1405 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1563 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11299 (p : Pattern) (guard : d0 p = 1) : d121 p ≤ (0 : Int) + d121 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11300 (p : Pattern) (guard : d4206 p = 1) : d122 p ≤ (0 : Int) + d121 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11298 p hg
    simpa only [d4206, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11299 p hg
    simpa only [d4206, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11301 (p : Pattern) (guard : d4206 p = 1) : d123 p ≤ (0 : Int) + d4916 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d123, d4916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11297 p hg
    simpa only [d123, d4916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d123, d4916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11300 p hg
    simpa only [d123, d4916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11302 (p : Pattern) (guard : d4206 p = 1) : d124 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1563 p hg
    simpa only [d4206, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4206, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11303 (p : Pattern) (guard : d4206 p = 1) : d125 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1321 p hg
    simpa only [d4206, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4206, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11304 (p : Pattern) (guard : d4206 p = 1) : d126 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11302 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11303 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11305 (p : Pattern) (guard : d4206 p = 1) : d127 p ≤ (0 : Int) + d4917 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d127, d4917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11301 p hg
    simpa only [d127, d4917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d127, d4917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11304 p hg
    simpa only [d127, d4917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11306 (p : Pattern) (guard : d4206 p = 1) : d128 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11253 p hg
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11307 (p : Pattern) (guard : d4206 p = 1) : d129 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11304 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11306 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11308 (p : Pattern) (guard : d4206 p = 1) : d130 p ≤ (0 : Int) + d4918 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d130, d4918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11305 p hg
    simpa only [d130, d4918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d130, d4918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11307 p hg
    simpa only [d130, d4918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11309 (p : Pattern) (guard : d4206 p = 1) : d131 p ≤ (0 : Int) + d4919 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d131, d4919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11294 p hg
    simpa only [d131, d4919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d131, d4919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11308 p hg
    simpa only [d131, d4919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11310 (p : Pattern) (guard : d4206 p = 1) : d132 p ≤ (0 : Int) + d117 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3020 p hg
    simpa only [d4206, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11296 p hg
    simpa only [d4206, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11311 (p : Pattern) (guard : d4206 p = 1) : d133 p ≤ (0 : Int) + d4238 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d133, d4238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11287 p hg
    simpa only [d133, d4238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d133, d4238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11310 p hg
    simpa only [d133, d4238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11312 (p : Pattern) (guard : d4206 p = 1) : d134 p ≤ (0 : Int) + d4239 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d134, d4239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11289 p hg
    simpa only [d134, d4239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d134, d4239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11243 p hg
    simpa only [d134, d4239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11313 (p : Pattern) (guard : d4206 p = 1) : d135 p ≤ (0 : Int) + d4240 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d135, d4240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11311 p hg
    simpa only [d135, d4240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d135, d4240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11312 p hg
    simpa only [d135, d4240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11314 (p : Pattern) (guard : d4206 p = 1) : d136 p ≤ (0 : Int) + d4241 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d136, d4241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11289 p hg
    simpa only [d136, d4241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d136, d4241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11245 p hg
    simpa only [d136, d4241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11315 (p : Pattern) (guard : d4206 p = 1) : d137 p ≤ (0 : Int) + d4242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d137, d4242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11314 p hg
    simpa only [d137, d4242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d137, d4242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d137, d4242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11316 (p : Pattern) (guard : d4206 p = 1) : d138 p ≤ (0 : Int) + d4243 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d138, d4243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11313 p hg
    simpa only [d138, d4243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d138, d4243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11315 p hg
    simpa only [d138, d4243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11317 (p : Pattern) (guard : d4206 p = 1) : d139 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1573 p hg
    simpa only [d4206, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4206, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11318 (p : Pattern) (guard : d4206 p = 1) : d140 p ≤ (0 : Int) + d4281 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d140, d4281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11300 p hg
    simpa only [d140, d4281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d140, d4281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11317 p hg
    simpa only [d140, d4281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11319 (p : Pattern) (guard : d4206 p = 1) : d141 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11303 p hg
    simpa only [d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11253 p hg
    simpa only [d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11320 (p : Pattern) (guard : d4206 p = 1) : d142 p ≤ (0 : Int) + d4282 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d142, d4282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11318 p hg
    simpa only [d142, d4282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d142, d4282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11319 p hg
    simpa only [d142, d4282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11321 (p : Pattern) (guard : d4206 p = 1) : d143 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11303 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11255 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11322 (p : Pattern) (guard : d4206 p = 1) : d144 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11321 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11323 (p : Pattern) (guard : d4206 p = 1) : d145 p ≤ (0 : Int) + d4920 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d145, d4920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11320 p hg
    simpa only [d145, d4920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d145, d4920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11322 p hg
    simpa only [d145, d4920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11324 (p : Pattern) (guard : d4206 p = 1) : d146 p ≤ (0 : Int) + d4921 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d146, d4921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11316 p hg
    simpa only [d146, d4921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d146, d4921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11323 p hg
    simpa only [d146, d4921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11325 (p : Pattern) (guard : d4206 p = 1) : d147 p ≤ (0 : Int) + d4922 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d147, d4922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11309 p hg
    simpa only [d147, d4922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d147, d4922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11324 p hg
    simpa only [d147, d4922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11326 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (0 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3159 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1282 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11327 (p : Pattern) (guard : d4206 p = 1) : d148 p ≤ (0 : Int) + d121 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11326 p hg
    simpa only [d4206, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11299 p hg
    simpa only [d4206, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11328 (p : Pattern) (guard : d4206 p = 1) : d149 p ≤ (0 : Int) + d4916 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d149, d4916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11310 p hg
    simpa only [d149, d4916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d149, d4916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11327 p hg
    simpa only [d149, d4916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11329 (p : Pattern) (guard : d4206 p = 1) : d150 p ≤ (0 : Int) + d4917 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d150, d4917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11328 p hg
    simpa only [d150, d4917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d150, d4917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d150, d4917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11330 (p : Pattern) (guard : d4206 p = 1) : d151 p ≤ (0 : Int) + d4918 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d151, d4918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11329 p hg
    simpa only [d151, d4918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d151, d4918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d151, d4918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11331 (p : Pattern) (guard : d4206 p = 1) : d152 p ≤ (0 : Int) + d4919 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d152, d4919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11294 p hg
    simpa only [d152, d4919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d152, d4919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11330 p hg
    simpa only [d152, d4919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11332 (p : Pattern) (guard : d4206 p = 1) : d153 p ≤ (0 : Int) + d4281 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d153, d4281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11327 p hg
    simpa only [d153, d4281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d153, d4281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d153, d4281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11333 (p : Pattern) (guard : d4206 p = 1) : d154 p ≤ (0 : Int) + d4282 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d154, d4282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11332 p hg
    simpa only [d154, d4282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d154, d4282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d154, d4282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11334 (p : Pattern) (guard : d4206 p = 1) : d155 p ≤ (0 : Int) + d4920 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d155, d4920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11333 p hg
    simpa only [d155, d4920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d155, d4920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d155, d4920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11335 (p : Pattern) (guard : d4206 p = 1) : d156 p ≤ (0 : Int) + d4921 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d156, d4921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11316 p hg
    simpa only [d156, d4921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d156, d4921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11334 p hg
    simpa only [d156, d4921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11336 (p : Pattern) (guard : d4206 p = 1) : d157 p ≤ (0 : Int) + d4922 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d157, d4922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11331 p hg
    simpa only [d157, d4922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d157, d4922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11335 p hg
    simpa only [d157, d4922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11337 (p : Pattern) (guard : d4206 p = 1) : d158 p ≤ (0 : Int) + d4922 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11325 p hg
    simpa only [d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11336 p hg
    simpa only [d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11338 (p : Pattern) (guard : d4206 p = 1) : d159 p ≤ (0 : Int) + d4245 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d159, d4245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11292 p hg
    simpa only [d159, d4245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d159, d4245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d159, d4245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11339 (p : Pattern) (guard : d4206 p = 1) : d160 p ≤ (0 : Int) + d4246 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d160, d4246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11338 p hg
    simpa only [d160, d4246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d160, d4246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d160, d4246, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
