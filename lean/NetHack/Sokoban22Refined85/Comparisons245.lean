/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons244
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare34300 (p : Pattern) (guard : d8117 p = 1) : d0 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34266 p hg
    simpa only [d8117, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34299 p hg
    simpa only [d8117, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34301 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d371 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34302 (p : Pattern) (guard : d8123 p = 1) : d0 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34300 p hg
    simpa only [d8123, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34301 p hg
    simpa only [d8123, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34303 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34304 (p : Pattern) (guard : d8129 p = 1) : d0 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34302 p hg
    simpa only [d8129, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34303 p hg
    simpa only [d8129, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34305 (p : Pattern) (guard : d8135 p = 1) : d0 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34304 p hg
    simpa only [d8135, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8135, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34306 (p : Pattern) (guard : d8136 p = 1) : d0 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34298 p hg
    simpa only [d8136, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34305 p hg
    simpa only [d8136, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34307 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34308 (p : Pattern) (guard : d8141 p = 1) : d0 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34238 p hg
    simpa only [d8141, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34307 p hg
    simpa only [d8141, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34309 (p : Pattern) (guard : d8142 p = 1) : d0 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34306 p hg
    simpa only [d8142, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34308 p hg
    simpa only [d8142, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34310 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34311 (p : Pattern) (guard : d8141 p = 1) : d0 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34284 p hg
    simpa only [d8141, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34310 p hg
    simpa only [d8141, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34312 (p : Pattern) (guard : d8147 p = 1) : d0 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8141 p = 1 := by simpa only [d8147, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34311 p hg
    simpa only [d8147, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8147, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8147, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34313 (p : Pattern) (guard : d8148 p = 1) : d0 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8142 p = 1 := by simpa only [d8148, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34309 p hg
    simpa only [d8148, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8147 p = 1 := by simpa only [d8148, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34312 p hg
    simpa only [d8148, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34314 (p : Pattern) (guard : d8149 p = 1) : d0 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8143 p = 1 := by simpa only [d8149, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34294 p hg
    simpa only [d8149, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8148 p = 1 := by simpa only [d8149, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34313 p hg
    simpa only [d8149, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34315 (p : Pattern) (guard : d8150 p = 1) : d0 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8144 p = 1 := by simpa only [d8150, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34242 p hg
    simpa only [d8150, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8149 p = 1 := by simpa only [d8150, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34314 p hg
    simpa only [d8150, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34316 (p : Pattern) (guard : d8151 p = 1) : d0 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8145 p = 1 := by simpa only [d8151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34198 p hg
    simpa only [d8151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8150 p = 1 := by simpa only [d8151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34315 p hg
    simpa only [d8151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34317 (p : Pattern) (guard : d8152 p = 1) : d0 p ≤ (0 : Int) + d447 p := by
  cases selected : p 48 with
  | false =>
    have hg : d8146 p = 1 := by simpa only [d8152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34199 p hg
    simpa only [d8152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8151 p = 1 := by simpa only [d8152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34316 p hg
    simpa only [d8152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34318 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d314 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33794 p hg
    simpa only [d14, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4500 p hg
    simpa only [d14, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34319 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33795 p hg
    simpa only [d14, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d14, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34320 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d316 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34318 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34319 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34321 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33799 p hg
    simpa only [d14, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d14, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34322 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34321 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34323 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d319 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34320 p hg
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34322 p hg
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34324 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34319 p hg
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34325 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34324 p hg
    simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34326 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d322 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34323 p hg
    simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34325 p hg
    simpa only [d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34327 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34322 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34328 (p : Pattern) (guard : d8086 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare34329 (p : Pattern) (guard : d8087 p = 1) : d15 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d15, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34327 p hg
    simpa only [d8087, d15, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d15, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34328 p hg
    simpa only [d8087, d15, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34330 (p : Pattern) (guard : d8088 p = 1) : d16 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8088, d16, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34326 p hg
    simpa only [d8088, d16, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8087 p = 1 := by simpa only [d8088, d16, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34329 p hg
    simpa only [d8088, d16, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34331 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d326 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33810 p hg
    simpa only [d14, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1493 p hg
    simpa only [d14, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34332 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33811 p hg
    simpa only [d14, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d14, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34333 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d328 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34331 p hg
    simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34332 p hg
    simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34334 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33816 p hg
    simpa only [d14, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d14, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34335 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34334 p hg
    simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34336 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34333 p hg
    simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34335 p hg
    simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34337 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34332 p hg
    simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34338 (p : Pattern) (guard : d5843 p = 1) : d13 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d5843, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34339 (p : Pattern) (guard : d8084 p = 1) : d14 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d8084, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34338 p hg
    simpa only [d8084, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34340 (p : Pattern) (guard : d8085 p = 1) : d14 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34339 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34341 (p : Pattern) (guard : d8086 p = 1) : d14 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34337 p hg
    simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34340 p hg
    simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34342 (p : Pattern) (guard : d8087 p = 1) : d14 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34336 p hg
    simpa only [d8087, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34341 p hg
    simpa only [d8087, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34343 (p : Pattern) (guard : d8086 p = 1) : d14 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34335 p hg
    simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34340 p hg
    simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34344 (p : Pattern) (guard : d8090 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare34345 (p : Pattern) (guard : d8091 p = 1) : d15 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d15, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34343 p hg
    simpa only [d8091, d15, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d15, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d15, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34346 (p : Pattern) (guard : d8092 p = 1) : d16 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d16, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34342 p hg
    simpa only [d8092, d16, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d16, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34345 p hg
    simpa only [d8092, d16, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34347 (p : Pattern) (guard : d8093 p = 1) : d16 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8088 p = 1 := by simpa only [d8093, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34330 p hg
    simpa only [d8093, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8092 p = 1 := by simpa only [d8093, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34346 p hg
    simpa only [d8093, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34348 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d339 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33829 p hg
    simpa only [d14, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d14, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34349 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d340 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34348 p hg
    simpa only [d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34350 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34349 p hg
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34337 p hg
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34351 (p : Pattern) (guard : d8086 p = 1) : d14 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d8086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34340 p hg
    simpa only [d8086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34352 (p : Pattern) (guard : d8087 p = 1) : d14 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34350 p hg
    simpa only [d8087, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34351 p hg
    simpa only [d8087, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34353 (p : Pattern) (guard : d8091 p = 1) : d15 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d15, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34341 p hg
    simpa only [d8091, d15, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d15, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d15, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34354 (p : Pattern) (guard : d8092 p = 1) : d16 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d16, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34352 p hg
    simpa only [d8092, d16, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d16, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34353 p hg
    simpa only [d8092, d16, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34355 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (0 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare920 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34356 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34355 p hg
    simpa only [d18, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d18, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34357 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34356 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare901 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34358 (p : Pattern) (guard : d5843 p = 1) : d17 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34359 (p : Pattern) (guard : d8084 p = 1) : d18 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d8084, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34358 p hg
    simpa only [d8084, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34360 (p : Pattern) (guard : d8085 p = 1) : d18 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare901 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34359 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34361 (p : Pattern) (guard : d8086 p = 1) : d18 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34357 p hg
    simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34360 p hg
    simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34362 (p : Pattern) (guard : d5843 p = 1) : d4 p ≤ (0 : Int) + d12 p := by
  change (4 : Int) ≤ (0 : Int) + 12
  decide
theorem compare34363 (p : Pattern) (guard : d5847 p = 1) : d18 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34362 p hg
    simpa only [d5847, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d5847, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34364 (p : Pattern) (guard : d8089 p = 1) : d18 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34359 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34363 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34365 (p : Pattern) (guard : d8090 p = 1) : d18 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34360 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34364 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34366 (p : Pattern) (guard : d8091 p = 1) : d18 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34361 p hg
    simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34365 p hg
    simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34367 (p : Pattern) (guard : d8094 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare34368 (p : Pattern) (guard : d8095 p = 1) : d19 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34365 p hg
    simpa only [d8095, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34369 (p : Pattern) (guard : d8096 p = 1) : d20 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d20, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34366 p hg
    simpa only [d8096, d20, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d20, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34368 p hg
    simpa only [d8096, d20, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34370 (p : Pattern) (guard : d8097 p = 1) : d21 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d21, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34354 p hg
    simpa only [d8097, d21, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d21, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34369 p hg
    simpa only [d8097, d21, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34371 (p : Pattern) (guard : d8098 p = 1) : d22 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8093 p = 1 := by simpa only [d8098, d22, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34347 p hg
    simpa only [d8098, d22, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8097 p = 1 := by simpa only [d8098, d22, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34370 p hg
    simpa only [d8098, d22, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34372 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d348 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33842 p hg
    simpa only [d14, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d14, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34373 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34372 p hg
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34374 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34373 p hg
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34375 (p : Pattern) (guard : d8087 p = 1) : d14 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34374 p hg
    simpa only [d8087, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34351 p hg
    simpa only [d8087, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34376 (p : Pattern) (guard : d8091 p = 1) : d15 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34351 p hg
    simpa only [d8091, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34377 (p : Pattern) (guard : d8092 p = 1) : d16 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d16, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34375 p hg
    simpa only [d8092, d16, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d16, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34376 p hg
    simpa only [d8092, d16, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34378 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (0 : Int) + d8 p := by
  change (4 : Int) ≤ (0 : Int) + 8
  decide
theorem compare34379 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (0 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34378 p hg
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34380 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34379 p hg
    simpa only [d18, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d18, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34381 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34380 p hg
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare901 p hg
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34382 (p : Pattern) (guard : d8086 p = 1) : d18 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34381 p hg
    simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34360 p hg
    simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34383 (p : Pattern) (guard : d8091 p = 1) : d18 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34382 p hg
    simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34365 p hg
    simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34384 (p : Pattern) (guard : d8096 p = 1) : d20 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d20, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34383 p hg
    simpa only [d8096, d20, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d20, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34368 p hg
    simpa only [d8096, d20, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34385 (p : Pattern) (guard : d8097 p = 1) : d21 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d21, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34377 p hg
    simpa only [d8097, d21, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d21, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34384 p hg
    simpa only [d8097, d21, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34386 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d24, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14548 p hg
    simpa only [d24, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d24, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare867 p hg
    simpa only [d24, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34387 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34386 p hg
    simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare868 p hg
    simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34388 (p : Pattern) (guard : d5843 p = 1) : d23 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare866 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34389 (p : Pattern) (guard : d8084 p = 1) : d24 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare866 p hg
    simpa only [d8084, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34388 p hg
    simpa only [d8084, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34390 (p : Pattern) (guard : d8085 p = 1) : d24 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare868 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34389 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34391 (p : Pattern) (guard : d8086 p = 1) : d24 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34387 p hg
    simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34390 p hg
    simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34392 (p : Pattern) (guard : d5843 p = 1) : d9 p ≤ (0 : Int) + d12 p := by
  change (9 : Int) ≤ (0 : Int) + 12
  decide
theorem compare34393 (p : Pattern) (guard : d5847 p = 1) : d24 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34392 p hg
    simpa only [d5847, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d5847, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34394 (p : Pattern) (guard : d8089 p = 1) : d24 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34389 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34393 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34395 (p : Pattern) (guard : d8090 p = 1) : d24 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34390 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34394 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34396 (p : Pattern) (guard : d8091 p = 1) : d24 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34391 p hg
    simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34395 p hg
    simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34397 (p : Pattern) (guard : d8095 p = 1) : d25 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34395 p hg
    simpa only [d8095, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34398 (p : Pattern) (guard : d8096 p = 1) : d26 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d26, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34396 p hg
    simpa only [d8096, d26, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d26, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34397 p hg
    simpa only [d8096, d26, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34399 (p : Pattern) (guard : d8101 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare34400 (p : Pattern) (guard : d8102 p = 1) : d27 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d27, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34398 p hg
    simpa only [d8102, d27, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d27, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34399 p hg
    simpa only [d8102, d27, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34401 (p : Pattern) (guard : d8103 p = 1) : d28 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d28, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34385 p hg
    simpa only [d8103, d28, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d28, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34400 p hg
    simpa only [d8103, d28, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34402 (p : Pattern) (guard : d8104 p = 1) : d29 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8098 p = 1 := by simpa only [d8104, d29, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34371 p hg
    simpa only [d8104, d29, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8103 p = 1 := by simpa only [d8104, d29, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34401 p hg
    simpa only [d8104, d29, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34403 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33863 p hg
    simpa only [d14, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d14, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34404 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34403 p hg
    simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34405 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34404 p hg
    simpa only [d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34406 (p : Pattern) (guard : d8087 p = 1) : d14 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34405 p hg
    simpa only [d8087, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34351 p hg
    simpa only [d8087, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34407 (p : Pattern) (guard : d5843 p = 1) : d30 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1506 p hg
    simpa only [d5843, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34408 (p : Pattern) (guard : d8084 p = 1) : d31 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1506 p hg
    simpa only [d8084, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34407 p hg
    simpa only [d8084, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34409 (p : Pattern) (guard : d8085 p = 1) : d31 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1508 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34408 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34410 (p : Pattern) (guard : d8086 p = 1) : d31 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1508 p hg
    simpa only [d8086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34409 p hg
    simpa only [d8086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34411 (p : Pattern) (guard : d8091 p = 1) : d32 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34410 p hg
    simpa only [d8091, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34412 (p : Pattern) (guard : d8092 p = 1) : d33 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d33, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34406 p hg
    simpa only [d8092, d33, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d33, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34411 p hg
    simpa only [d8092, d33, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34413 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33853 p hg
    simpa only [d14, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d14, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34414 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34413 p hg
    simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1500 p hg
    simpa only [d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34415 (p : Pattern) (guard : d8086 p = 1) : d14 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34414 p hg
    simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34340 p hg
    simpa only [d8086, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34416 (p : Pattern) (guard : d5847 p = 1) : d14 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34004 p hg
    simpa only [d5847, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17644 p hg
    simpa only [d5847, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34417 (p : Pattern) (guard : d8089 p = 1) : d14 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34339 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34416 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34418 (p : Pattern) (guard : d8090 p = 1) : d14 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34340 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34417 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34419 (p : Pattern) (guard : d8091 p = 1) : d14 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34415 p hg
    simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34418 p hg
    simpa only [d8091, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34420 (p : Pattern) (guard : d5843 p = 1) : d34 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare955 p hg
    simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34421 (p : Pattern) (guard : d8084 p = 1) : d35 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare955 p hg
    simpa only [d8084, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34420 p hg
    simpa only [d8084, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34422 (p : Pattern) (guard : d8085 p = 1) : d35 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare957 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34421 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34423 (p : Pattern) (guard : d5843 p = 1) : d6 p ≤ (0 : Int) + d12 p := by
  change (6 : Int) ≤ (0 : Int) + 12
  decide
theorem compare34424 (p : Pattern) (guard : d5847 p = 1) : d35 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34423 p hg
    simpa only [d5847, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17677 p hg
    simpa only [d5847, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34425 (p : Pattern) (guard : d8089 p = 1) : d35 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34421 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34424 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34426 (p : Pattern) (guard : d8090 p = 1) : d35 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34422 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34425 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34427 (p : Pattern) (guard : d8095 p = 1) : d36 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34426 p hg
    simpa only [d8095, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34428 (p : Pattern) (guard : d8096 p = 1) : d37 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d37, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34419 p hg
    simpa only [d8096, d37, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d37, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34427 p hg
    simpa only [d8096, d37, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34429 (p : Pattern) (guard : d8097 p = 1) : d38 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d38, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34412 p hg
    simpa only [d8097, d38, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d38, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34428 p hg
    simpa only [d8097, d38, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34430 (p : Pattern) (guard : d8091 p = 1) : d14 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34343 p hg
    simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34418 p hg
    simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34431 (p : Pattern) (guard : d5843 p = 1) : d39 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare709 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34432 (p : Pattern) (guard : d8084 p = 1) : d40 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare709 p hg
    simpa only [d8084, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34431 p hg
    simpa only [d8084, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34433 (p : Pattern) (guard : d8085 p = 1) : d40 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare711 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34432 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34434 (p : Pattern) (guard : d5843 p = 1) : d11 p ≤ (0 : Int) + d12 p := by
  change (11 : Int) ≤ (0 : Int) + 12
  decide
theorem compare34435 (p : Pattern) (guard : d5847 p = 1) : d40 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34434 p hg
    simpa only [d5847, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17682 p hg
    simpa only [d5847, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34436 (p : Pattern) (guard : d8089 p = 1) : d40 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34432 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34435 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34437 (p : Pattern) (guard : d8090 p = 1) : d40 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34433 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34436 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34438 (p : Pattern) (guard : d8095 p = 1) : d41 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34437 p hg
    simpa only [d8095, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34439 (p : Pattern) (guard : d8096 p = 1) : d42 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d42, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34430 p hg
    simpa only [d8096, d42, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d42, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34438 p hg
    simpa only [d8096, d42, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
