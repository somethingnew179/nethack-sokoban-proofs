/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare280 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (1 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare274 p hg
    simpa only [d21, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare279 p hg
    simpa only [d21, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare281 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (1 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare274 p hg
    simpa only [d22, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare280 p hg
    simpa only [d22, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare282 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (1 : Int) + d10 p := by
  change (9 : Int) ≤ (1 : Int) + 10
  decide
theorem compare283 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (1 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d23, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d23, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare284 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (1 : Int) + d58 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d24, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d24, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d24, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare283 p hg
    simpa only [d24, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare285 (p : Pattern) (guard : d1 p = 1) : d25 p ≤ (1 : Int) + d59 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d25, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare284 p hg
    simpa only [d25, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d25, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d25, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare286 (p : Pattern) (guard : d1 p = 1) : d26 p ≤ (1 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d26, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare284 p hg
    simpa only [d26, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d26, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare285 p hg
    simpa only [d26, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare287 (p : Pattern) (guard : d1 p = 1) : d27 p ≤ (1 : Int) + d112 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d27, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare286 p hg
    simpa only [d27, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d27, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d27, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare288 (p : Pattern) (guard : d1 p = 1) : d28 p ≤ (1 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d28, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare280 p hg
    simpa only [d28, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d28, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare287 p hg
    simpa only [d28, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare289 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (1 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d29, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare281 p hg
    simpa only [d29, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare288 p hg
    simpa only [d29, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare290 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (1 : Int) + d3 p := by
  change (2 : Int) ≤ (1 : Int) + 3
  decide
theorem compare291 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (1 : Int) + d115 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare290 p hg
    simpa only [d30, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d30, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare292 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (1 : Int) + d116 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare290 p hg
    simpa only [d31, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare291 p hg
    simpa only [d31, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare293 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (1 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare292 p hg
    simpa only [d32, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d32, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare294 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (1 : Int) + d118 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d33, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare272 p hg
    simpa only [d33, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d33, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare293 p hg
    simpa only [d33, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare295 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (1 : Int) + d7 p := by
  change (6 : Int) ≤ (1 : Int) + 7
  decide
theorem compare296 (p : Pattern) (guard : d1 p = 1) : d34 p ≤ (1 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare295 p hg
    simpa only [d34, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d34, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare297 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (1 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d35, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare295 p hg
    simpa only [d35, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d35, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare296 p hg
    simpa only [d35, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare298 (p : Pattern) (guard : d1 p = 1) : d36 p ≤ (1 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d36, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare297 p hg
    simpa only [d36, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d36, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d36, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare299 (p : Pattern) (guard : d1 p = 1) : d37 p ≤ (1 : Int) + d122 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d37, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare272 p hg
    simpa only [d37, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d37, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare298 p hg
    simpa only [d37, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare300 (p : Pattern) (guard : d1 p = 1) : d38 p ≤ (1 : Int) + d123 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d38, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare294 p hg
    simpa only [d38, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d38, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare299 p hg
    simpa only [d38, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare301 (p : Pattern) (guard : d1 p = 1) : d42 p ≤ (1 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d42, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare272 p hg
    simpa only [d42, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d42, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare96 p hg
    simpa only [d42, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare302 (p : Pattern) (guard : d1 p = 1) : d43 p ≤ (1 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d43, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare277 p hg
    simpa only [d43, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d43, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d43, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare303 (p : Pattern) (guard : d1 p = 1) : d44 p ≤ (1 : Int) + d126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d44, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare301 p hg
    simpa only [d44, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d44, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare302 p hg
    simpa only [d44, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare304 (p : Pattern) (guard : d1 p = 1) : d45 p ≤ (1 : Int) + d127 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d45, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare300 p hg
    simpa only [d45, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d45, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare303 p hg
    simpa only [d45, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare305 (p : Pattern) (guard : d1 p = 1) : d46 p ≤ (1 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d46, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare272 p hg
    simpa only [d46, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d46, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d46, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare306 (p : Pattern) (guard : d1 p = 1) : d47 p ≤ (1 : Int) + d126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d47, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare305 p hg
    simpa only [d47, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d47, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare302 p hg
    simpa only [d47, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare307 (p : Pattern) (guard : d1 p = 1) : d48 p ≤ (1 : Int) + d70 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d48, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare284 p hg
    simpa only [d48, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d48, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d48, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare308 (p : Pattern) (guard : d1 p = 1) : d49 p ≤ (1 : Int) + d128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d49, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare307 p hg
    simpa only [d49, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d49, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d49, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare309 (p : Pattern) (guard : d1 p = 1) : d50 p ≤ (1 : Int) + d129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d50, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare306 p hg
    simpa only [d50, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d50, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare308 p hg
    simpa only [d50, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare310 (p : Pattern) (guard : d1 p = 1) : d51 p ≤ (1 : Int) + d130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d51, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare304 p hg
    simpa only [d51, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d51, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare309 p hg
    simpa only [d51, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare311 (p : Pattern) (guard : d1 p = 1) : d52 p ≤ (1 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d52, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare289 p hg
    simpa only [d52, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d52, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare310 p hg
    simpa only [d52, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare312 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (1 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d53, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare292 p hg
    simpa only [d53, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d53, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare293 p hg
    simpa only [d53, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare313 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (1 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare274 p hg
    simpa only [d54, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare312 p hg
    simpa only [d54, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare314 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (1 : Int) + d134 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d55, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare279 p hg
    simpa only [d55, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d55, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare286 p hg
    simpa only [d55, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare315 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (1 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare313 p hg
    simpa only [d56, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare314 p hg
    simpa only [d56, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare316 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (1 : Int) + d11 p := by
  change (10 : Int) ≤ (1 : Int) + 11
  decide
theorem compare317 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (1 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare316 p hg
    simpa only [d57, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d57, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare318 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (1 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare316 p hg
    simpa only [d58, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare317 p hg
    simpa only [d58, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare319 (p : Pattern) (guard : d1 p = 1) : d59 p ≤ (1 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare318 p hg
    simpa only [d59, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d59, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare320 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (1 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d60, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare318 p hg
    simpa only [d60, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d60, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare319 p hg
    simpa only [d60, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare321 (p : Pattern) (guard : d1 p = 1) : d61 p ≤ (1 : Int) + d136 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare279 p hg
    simpa only [d61, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare320 p hg
    simpa only [d61, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare322 (p : Pattern) (guard : d1 p = 1) : d64 p ≤ (1 : Int) + d137 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d64, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare321 p hg
    simpa only [d64, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d64, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare98 p hg
    simpa only [d64, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare323 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (1 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare315 p hg
    simpa only [d65, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare322 p hg
    simpa only [d65, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare324 (p : Pattern) (guard : d1 p = 1) : d66 p ≤ (1 : Int) + d139 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d66, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare292 p hg
    simpa only [d66, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d66, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d66, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare325 (p : Pattern) (guard : d1 p = 1) : d67 p ≤ (1 : Int) + d140 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d67, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare299 p hg
    simpa only [d67, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d67, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare324 p hg
    simpa only [d67, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare326 (p : Pattern) (guard : d1 p = 1) : d68 p ≤ (1 : Int) + d141 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare302 p hg
    simpa only [d68, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare307 p hg
    simpa only [d68, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare327 (p : Pattern) (guard : d1 p = 1) : d69 p ≤ (1 : Int) + d142 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d69, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare325 p hg
    simpa only [d69, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d69, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare326 p hg
    simpa only [d69, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare328 (p : Pattern) (guard : d1 p = 1) : d70 p ≤ (1 : Int) + d72 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d70, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare318 p hg
    simpa only [d70, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d70, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d70, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare329 (p : Pattern) (guard : d1 p = 1) : d71 p ≤ (1 : Int) + d143 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d71, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare302 p hg
    simpa only [d71, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d71, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare328 p hg
    simpa only [d71, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare330 (p : Pattern) (guard : d1 p = 1) : d74 p ≤ (1 : Int) + d144 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d74, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare329 p hg
    simpa only [d74, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d74, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare71 p hg
    simpa only [d74, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare331 (p : Pattern) (guard : d1 p = 1) : d75 p ≤ (1 : Int) + d145 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d75, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare327 p hg
    simpa only [d75, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d75, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare330 p hg
    simpa only [d75, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare332 (p : Pattern) (guard : d1 p = 1) : d76 p ≤ (1 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d76, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare323 p hg
    simpa only [d76, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d76, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare331 p hg
    simpa only [d76, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare333 (p : Pattern) (guard : d1 p = 1) : d77 p ≤ (1 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d77, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare311 p hg
    simpa only [d77, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d77, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare332 p hg
    simpa only [d77, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare334 (p : Pattern) (guard : d1 p = 1) : d78 p ≤ (1 : Int) + d148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d78, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare297 p hg
    simpa only [d78, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d78, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare298 p hg
    simpa only [d78, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare335 (p : Pattern) (guard : d1 p = 1) : d79 p ≤ (1 : Int) + d149 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d79, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare312 p hg
    simpa only [d79, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d79, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare334 p hg
    simpa only [d79, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare336 (p : Pattern) (guard : d1 p = 1) : d80 p ≤ (1 : Int) + d150 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d80, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare335 p hg
    simpa only [d80, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d80, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare98 p hg
    simpa only [d80, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare337 (p : Pattern) (guard : d1 p = 1) : d81 p ≤ (1 : Int) + d151 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d81, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare336 p hg
    simpa only [d81, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d81, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d81, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare338 (p : Pattern) (guard : d1 p = 1) : d82 p ≤ (1 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d82, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare289 p hg
    simpa only [d82, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d82, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare337 p hg
    simpa only [d82, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare339 (p : Pattern) (guard : d1 p = 1) : d83 p ≤ (1 : Int) + d153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d83, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare334 p hg
    simpa only [d83, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d83, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d83, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare340 (p : Pattern) (guard : d1 p = 1) : d84 p ≤ (1 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d84, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare339 p hg
    simpa only [d84, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d84, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d84, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare341 (p : Pattern) (guard : d1 p = 1) : d85 p ≤ (1 : Int) + d155 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d85, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare340 p hg
    simpa only [d85, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d85, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d85, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare342 (p : Pattern) (guard : d1 p = 1) : d86 p ≤ (1 : Int) + d156 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d86, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare323 p hg
    simpa only [d86, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d86, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare341 p hg
    simpa only [d86, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare343 (p : Pattern) (guard : d1 p = 1) : d87 p ≤ (1 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d87, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare338 p hg
    simpa only [d87, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d87, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare342 p hg
    simpa only [d87, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare344 (p : Pattern) (guard : d1 p = 1) : d88 p ≤ (1 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d88, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare333 p hg
    simpa only [d88, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d88, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare343 p hg
    simpa only [d88, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare345 (p : Pattern) (guard : d1 p = 1) : d89 p ≤ (1 : Int) + d112 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d89, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare286 p hg
    simpa only [d89, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d89, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare97 p hg
    simpa only [d89, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare346 (p : Pattern) (guard : d1 p = 1) : d90 p ≤ (1 : Int) + d159 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d90, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare345 p hg
    simpa only [d90, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d90, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare98 p hg
    simpa only [d90, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare347 (p : Pattern) (guard : d1 p = 1) : d91 p ≤ (1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare98 p hg
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare348 (p : Pattern) (guard : d1 p = 1) : d92 p ≤ (1 : Int) + d160 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d92, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare346 p hg
    simpa only [d92, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d92, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare347 p hg
    simpa only [d92, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare349 (p : Pattern) (guard : d1 p = 1) : d93 p ≤ (1 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare347 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare350 (p : Pattern) (guard : d1 p = 1) : d94 p ≤ (1 : Int) + d161 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d94, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare348 p hg
    simpa only [d94, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d94, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare349 p hg
    simpa only [d94, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare351 (p : Pattern) (guard : d1 p = 1) : d95 p ≤ (1 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare349 p hg
    simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare352 (p : Pattern) (guard : d1 p = 1) : d96 p ≤ (1 : Int) + d162 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d96, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare350 p hg
    simpa only [d96, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d96, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare351 p hg
    simpa only [d96, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare353 (p : Pattern) (guard : d1 p = 1) : d97 p ≤ (1 : Int) + d163 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d97, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare343 p hg
    simpa only [d97, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d97, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare352 p hg
    simpa only [d97, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare354 (p : Pattern) (guard : d1 p = 1) : d98 p ≤ (1 : Int) + d164 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d98, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare344 p hg
    simpa only [d98, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d98, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare353 p hg
    simpa only [d98, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare355 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (1 : Int) + d1 p := by
  change (2 : Int) ≤ (1 : Int) + 1
  decide
theorem compare356 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (1 : Int) + d102 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare355 p hg
    simpa only [d30, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d30, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare357 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (1 : Int) + d103 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare355 p hg
    simpa only [d31, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare356 p hg
    simpa only [d31, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare358 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (1 : Int) + d118 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d53, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare357 p hg
    simpa only [d53, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d53, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare293 p hg
    simpa only [d53, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare359 (p : Pattern) (guard : d1 p = 1) : d170 p ≤ (1 : Int) + d122 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d170, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare357 p hg
    simpa only [d170, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d170, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare298 p hg
    simpa only [d170, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare360 (p : Pattern) (guard : d1 p = 1) : d171 p ≤ (1 : Int) + d123 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d171, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare358 p hg
    simpa only [d171, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d171, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare359 p hg
    simpa only [d171, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare361 (p : Pattern) (guard : d1 p = 1) : d172 p ≤ (1 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d172, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare357 p hg
    simpa only [d172, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d172, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare96 p hg
    simpa only [d172, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare362 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (1 : Int) + d5 p := by
  change (6 : Int) ≤ (1 : Int) + 5
  decide
theorem compare363 (p : Pattern) (guard : d1 p = 1) : d34 p ≤ (1 : Int) + d106 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare362 p hg
    simpa only [d34, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d34, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare364 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (1 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d35, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare362 p hg
    simpa only [d35, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d35, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare363 p hg
    simpa only [d35, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare365 (p : Pattern) (guard : d1 p = 1) : d173 p ≤ (1 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d173, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare364 p hg
    simpa only [d173, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d173, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d173, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare366 (p : Pattern) (guard : d1 p = 1) : d174 p ≤ (1 : Int) + d126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d174, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare361 p hg
    simpa only [d174, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d174, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare365 p hg
    simpa only [d174, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare367 (p : Pattern) (guard : d1 p = 1) : d175 p ≤ (1 : Int) + d127 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d175, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare360 p hg
    simpa only [d175, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d175, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare366 p hg
    simpa only [d175, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare368 (p : Pattern) (guard : d1 p = 1) : d66 p ≤ (1 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d66, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare357 p hg
    simpa only [d66, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d66, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d66, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare369 (p : Pattern) (guard : d1 p = 1) : d176 p ≤ (1 : Int) + d126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d176, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare368 p hg
    simpa only [d176, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d176, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare365 p hg
    simpa only [d176, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare370 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (1 : Int) + d10 p := by
  change (11 : Int) ≤ (1 : Int) + 10
  decide
theorem compare371 (p : Pattern) (guard : d1 p = 1) : d39 p ≤ (1 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare370 p hg
    simpa only [d39, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d39, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare372 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (1 : Int) + d58 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d40, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare370 p hg
    simpa only [d40, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d40, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare371 p hg
    simpa only [d40, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare373 (p : Pattern) (guard : d1 p = 1) : d72 p ≤ (1 : Int) + d70 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d72, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare372 p hg
    simpa only [d72, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d72, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d72, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare374 (p : Pattern) (guard : d1 p = 1) : d73 p ≤ (1 : Int) + d128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d73, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare373 p hg
    simpa only [d73, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d73, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d73, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare375 (p : Pattern) (guard : d1 p = 1) : d177 p ≤ (1 : Int) + d129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d177, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare369 p hg
    simpa only [d177, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d177, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare374 p hg
    simpa only [d177, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare376 (p : Pattern) (guard : d1 p = 1) : d178 p ≤ (1 : Int) + d130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d178, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare367 p hg
    simpa only [d178, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d178, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare375 p hg
    simpa only [d178, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare377 (p : Pattern) (guard : d1 p = 1) : d179 p ≤ (1 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d179, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare289 p hg
    simpa only [d179, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d179, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare376 p hg
    simpa only [d179, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare378 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (1 : Int) + d3 p := by
  change (4 : Int) ≤ (1 : Int) + 3
  decide
theorem compare379 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (1 : Int) + d115 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare378 p hg
    simpa only [d17, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d17, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare380 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (1 : Int) + d116 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare378 p hg
    simpa only [d18, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare379 p hg
    simpa only [d18, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare381 (p : Pattern) (guard : d1 p = 1) : d43 p ≤ (1 : Int) + d139 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d43, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare380 p hg
    simpa only [d43, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d43, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d43, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare382 (p : Pattern) (guard : d1 p = 1) : d180 p ≤ (1 : Int) + d140 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d180, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare359 p hg
    simpa only [d180, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d180, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare381 p hg
    simpa only [d180, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare383 (p : Pattern) (guard : d1 p = 1) : d181 p ≤ (1 : Int) + d141 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d181, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare365 p hg
    simpa only [d181, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d181, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare373 p hg
    simpa only [d181, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare384 (p : Pattern) (guard : d1 p = 1) : d182 p ≤ (1 : Int) + d142 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d182, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare382 p hg
    simpa only [d182, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d182, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare383 p hg
    simpa only [d182, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare385 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (1 : Int) + d11 p := by
  change (12 : Int) ≤ (1 : Int) + 11
  decide
theorem compare386 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (1 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare385 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare387 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (1 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare385 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare386 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare388 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (1 : Int) + d72 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare387 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare389 (p : Pattern) (guard : d1 p = 1) : d183 p ≤ (1 : Int) + d143 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d183, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare365 p hg
    simpa only [d183, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d183, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare388 p hg
    simpa only [d183, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare390 (p : Pattern) (guard : d1 p = 1) : d184 p ≤ (1 : Int) + d144 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d184, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare389 p hg
    simpa only [d184, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d184, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d184, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare391 (p : Pattern) (guard : d1 p = 1) : d185 p ≤ (1 : Int) + d145 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d185, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare384 p hg
    simpa only [d185, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d185, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare390 p hg
    simpa only [d185, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare392 (p : Pattern) (guard : d1 p = 1) : d186 p ≤ (1 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d186, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare323 p hg
    simpa only [d186, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d186, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare391 p hg
    simpa only [d186, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare393 (p : Pattern) (guard : d1 p = 1) : d187 p ≤ (1 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d187, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare377 p hg
    simpa only [d187, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d187, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare392 p hg
    simpa only [d187, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare394 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (1 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare357 p hg
    simpa only [d32, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d32, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare395 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (1 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d53, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare357 p hg
    simpa only [d53, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d53, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare394 p hg
    simpa only [d53, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare396 (p : Pattern) (guard : d1 p = 1) : d36 p ≤ (1 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d36, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare364 p hg
    simpa only [d36, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d36, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d36, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare397 (p : Pattern) (guard : d1 p = 1) : d78 p ≤ (1 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d78, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare364 p hg
    simpa only [d78, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d78, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare396 p hg
    simpa only [d78, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare398 (p : Pattern) (guard : d1 p = 1) : d79 p ≤ (1 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d79, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare395 p hg
    simpa only [d79, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d79, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare397 p hg
    simpa only [d79, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare399 (p : Pattern) (guard : d1 p = 1) : d188 p ≤ (1 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d188, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare274 p hg
    simpa only [d188, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d188, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare398 p hg
    simpa only [d188, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare400 (p : Pattern) (guard : d1 p = 1) : d41 p ≤ (1 : Int) + d59 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d41, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare372 p hg
    simpa only [d41, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d41, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d41, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare401 (p : Pattern) (guard : d1 p = 1) : d62 p ≤ (1 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d62, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare372 p hg
    simpa only [d62, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d62, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare400 p hg
    simpa only [d62, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare402 (p : Pattern) (guard : d1 p = 1) : d63 p ≤ (1 : Int) + d112 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d63, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare401 p hg
    simpa only [d63, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d63, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d63, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare403 (p : Pattern) (guard : d1 p = 1) : d80 p ≤ (1 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d80, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare398 p hg
    simpa only [d80, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d80, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare402 p hg
    simpa only [d80, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare404 (p : Pattern) (guard : d1 p = 1) : d189 p ≤ (1 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d189, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare399 p hg
    simpa only [d189, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d189, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare403 p hg
    simpa only [d189, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare405 (p : Pattern) (guard : d1 p = 1) : d19 p ≤ (1 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare380 p hg
    simpa only [d19, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d19, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare406 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (1 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare380 p hg
    simpa only [d20, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare405 p hg
    simpa only [d20, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare407 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (1 : Int) + d7 p := by
  change (8 : Int) ≤ (1 : Int) + 7
  decide
theorem compare408 (p : Pattern) (guard : d1 p = 1) : d190 p ≤ (1 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d190, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare407 p hg
    simpa only [d190, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d190, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d190, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare409 (p : Pattern) (guard : d1 p = 1) : d191 p ≤ (1 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d191, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare407 p hg
    simpa only [d191, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d191, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare408 p hg
    simpa only [d191, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare410 (p : Pattern) (guard : d1 p = 1) : d192 p ≤ (1 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d192, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare409 p hg
    simpa only [d192, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d192, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d192, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare411 (p : Pattern) (guard : d1 p = 1) : d193 p ≤ (1 : Int) + d148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d193, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare409 p hg
    simpa only [d193, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d193, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare410 p hg
    simpa only [d193, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare412 (p : Pattern) (guard : d1 p = 1) : d194 p ≤ (1 : Int) + d149 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d194, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare406 p hg
    simpa only [d194, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d194, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare411 p hg
    simpa only [d194, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare413 (p : Pattern) (guard : d1 p = 1) : d195 p ≤ (1 : Int) + d150 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d195, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare412 p hg
    simpa only [d195, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d195, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d195, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare414 (p : Pattern) (guard : d1 p = 1) : d196 p ≤ (1 : Int) + d151 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d196, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare413 p hg
    simpa only [d196, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d196, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d196, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare415 (p : Pattern) (guard : d1 p = 1) : d197 p ≤ (1 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d197, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare404 p hg
    simpa only [d197, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d197, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare414 p hg
    simpa only [d197, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare416 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (1 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare395 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare312 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare417 (p : Pattern) (guard : d1 p = 1) : d198 p ≤ (1 : Int) + d134 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d198, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare279 p hg
    simpa only [d198, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d198, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare401 p hg
    simpa only [d198, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare418 (p : Pattern) (guard : d1 p = 1) : d199 p ≤ (1 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d199, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare416 p hg
    simpa only [d199, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d199, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare417 p hg
    simpa only [d199, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare419 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (1 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare387 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
