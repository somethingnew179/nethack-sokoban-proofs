/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons292
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare41020 (p : Pattern) (guard : d8112 p = 1) : d2263 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2263, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41016 p hg
    simpa only [d8112, d2263, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2263, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41019 p hg
    simpa only [d8112, d2263, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41021 (p : Pattern) (guard : d8099 p = 1) : d2196 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2196, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35523 p hg
    simpa only [d8099, d2196, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2196, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2196, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41022 (p : Pattern) (guard : d8105 p = 1) : d2196 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41021 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40417 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41023 (p : Pattern) (guard : d8111 p = 1) : d2198 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2198, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41022 p hg
    simpa only [d8111, d2198, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2198, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40460 p hg
    simpa only [d8111, d2198, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41024 (p : Pattern) (guard : d8117 p = 1) : d2234 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2234, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41023 p hg
    simpa only [d8117, d2234, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2234, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40481 p hg
    simpa only [d8117, d2234, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41025 (p : Pattern) (guard : d8118 p = 1) : d2264 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2264, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41020 p hg
    simpa only [d8118, d2264, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2264, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41024 p hg
    simpa only [d8118, d2264, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41026 (p : Pattern) (guard : d8117 p = 1) : d2239 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2239, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40983 p hg
    simpa only [d8117, d2239, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2239, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40484 p hg
    simpa only [d8117, d2239, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41027 (p : Pattern) (guard : d8123 p = 1) : d2242 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2242, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41026 p hg
    simpa only [d8123, d2242, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2242, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40486 p hg
    simpa only [d8123, d2242, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41028 (p : Pattern) (guard : d8124 p = 1) : d2265 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2265, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41025 p hg
    simpa only [d8124, d2265, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2265, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41027 p hg
    simpa only [d8124, d2265, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41029 (p : Pattern) (guard : d0 p = 1) : d2219 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41030 (p : Pattern) (guard : d8117 p = 1) : d2414 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41004 p hg
    simpa only [d8117, d2414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41029 p hg
    simpa only [d8117, d2414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41031 (p : Pattern) (guard : d0 p = 1) : d2415 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41032 (p : Pattern) (guard : d8123 p = 1) : d2416 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41030 p hg
    simpa only [d8123, d2416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41031 p hg
    simpa only [d8123, d2416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41033 (p : Pattern) (guard : d0 p = 1) : d2418 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41034 (p : Pattern) (guard : d8129 p = 1) : d2419 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41032 p hg
    simpa only [d8129, d2419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41033 p hg
    simpa only [d8129, d2419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41035 (p : Pattern) (guard : d8130 p = 1) : d2420 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2420, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41028 p hg
    simpa only [d8130, d2420, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2420, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41034 p hg
    simpa only [d8130, d2420, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41036 (p : Pattern) (guard : d8131 p = 1) : d2421 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2421, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41013 p hg
    simpa only [d8131, d2421, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2421, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41035 p hg
    simpa only [d8131, d2421, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41037 (p : Pattern) (guard : d0 p = 1) : d2185 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41038 (p : Pattern) (guard : d8105 p = 1) : d2185 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40412 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41037 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41039 (p : Pattern) (guard : d0 p = 1) : d2187 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41040 (p : Pattern) (guard : d8111 p = 1) : d2201 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41038 p hg
    simpa only [d8111, d2201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41039 p hg
    simpa only [d8111, d2201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41041 (p : Pattern) (guard : d8112 p = 1) : d2201 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40620 p hg
    simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41040 p hg
    simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41042 (p : Pattern) (guard : d0 p = 1) : d2258 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41043 (p : Pattern) (guard : d8117 p = 1) : d2259 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40479 p hg
    simpa only [d8117, d2259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41042 p hg
    simpa only [d8117, d2259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41044 (p : Pattern) (guard : d8118 p = 1) : d2422 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2422, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41041 p hg
    simpa only [d8118, d2422, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2422, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41043 p hg
    simpa only [d8118, d2422, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41045 (p : Pattern) (guard : d8123 p = 1) : d2260 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41043 p hg
    simpa only [d8123, d2260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40486 p hg
    simpa only [d8123, d2260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41046 (p : Pattern) (guard : d8124 p = 1) : d2423 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2423, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41044 p hg
    simpa only [d8124, d2423, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2423, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41045 p hg
    simpa only [d8124, d2423, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41047 (p : Pattern) (guard : d0 p = 1) : d2426 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41048 (p : Pattern) (guard : d8117 p = 1) : d2427 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40461 p hg
    simpa only [d8117, d2427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41047 p hg
    simpa only [d8117, d2427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41049 (p : Pattern) (guard : d8123 p = 1) : d2428 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41048 p hg
    simpa only [d8123, d2428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41050 (p : Pattern) (guard : d8129 p = 1) : d2429 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41049 p hg
    simpa only [d8129, d2429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d2429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41051 (p : Pattern) (guard : d8130 p = 1) : d2430 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2430, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41046 p hg
    simpa only [d8130, d2430, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2430, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41050 p hg
    simpa only [d8130, d2430, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41052 (p : Pattern) (guard : d0 p = 1) : d2232 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41053 (p : Pattern) (guard : d8117 p = 1) : d2232 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40958 p hg
    simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41052 p hg
    simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41054 (p : Pattern) (guard : d0 p = 1) : d2431 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41055 (p : Pattern) (guard : d8123 p = 1) : d2432 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2432, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41053 p hg
    simpa only [d8123, d2432, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2432, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41054 p hg
    simpa only [d8123, d2432, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41056 (p : Pattern) (guard : d0 p = 1) : d2267 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41057 (p : Pattern) (guard : d8129 p = 1) : d2433 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2433, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41055 p hg
    simpa only [d8129, d2433, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2433, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41056 p hg
    simpa only [d8129, d2433, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41058 (p : Pattern) (guard : d0 p = 1) : d2436 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41059 (p : Pattern) (guard : d8135 p = 1) : d2437 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2437, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41057 p hg
    simpa only [d8135, d2437, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2437, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41058 p hg
    simpa only [d8135, d2437, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41060 (p : Pattern) (guard : d8136 p = 1) : d2438 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2438, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41051 p hg
    simpa only [d8136, d2438, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2438, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41059 p hg
    simpa only [d8136, d2438, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41061 (p : Pattern) (guard : d8137 p = 1) : d2439 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2439, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41036 p hg
    simpa only [d8137, d2439, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2439, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41060 p hg
    simpa only [d8137, d2439, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41062 (p : Pattern) (guard : d8099 p = 1) : d2185 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2185, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35550 p hg
    simpa only [d8099, d2185, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2185, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2185, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41063 (p : Pattern) (guard : d8105 p = 1) : d2185 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41062 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41037 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41064 (p : Pattern) (guard : d8111 p = 1) : d2201 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2201, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41063 p hg
    simpa only [d8111, d2201, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2201, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41039 p hg
    simpa only [d8111, d2201, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41065 (p : Pattern) (guard : d8112 p = 1) : d2201 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40955 p hg
    simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41064 p hg
    simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41066 (p : Pattern) (guard : d8118 p = 1) : d2422 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2422, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41065 p hg
    simpa only [d8118, d2422, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2422, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41043 p hg
    simpa only [d8118, d2422, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41067 (p : Pattern) (guard : d8124 p = 1) : d2423 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2423, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41066 p hg
    simpa only [d8124, d2423, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2423, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41045 p hg
    simpa only [d8124, d2423, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41068 (p : Pattern) (guard : d8130 p = 1) : d2430 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2430, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41067 p hg
    simpa only [d8130, d2430, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2430, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41050 p hg
    simpa only [d8130, d2430, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41069 (p : Pattern) (guard : d8117 p = 1) : d2232 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40979 p hg
    simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41052 p hg
    simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41070 (p : Pattern) (guard : d8123 p = 1) : d2432 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2432, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41069 p hg
    simpa only [d8123, d2432, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2432, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41054 p hg
    simpa only [d8123, d2432, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41071 (p : Pattern) (guard : d8129 p = 1) : d2433 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2433, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41070 p hg
    simpa only [d8129, d2433, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2433, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41056 p hg
    simpa only [d8129, d2433, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41072 (p : Pattern) (guard : d8135 p = 1) : d2437 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2437, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41071 p hg
    simpa only [d8135, d2437, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2437, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41058 p hg
    simpa only [d8135, d2437, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41073 (p : Pattern) (guard : d8136 p = 1) : d2438 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2438, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41068 p hg
    simpa only [d8136, d2438, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2438, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41072 p hg
    simpa only [d8136, d2438, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41074 (p : Pattern) (guard : d8142 p = 1) : d2440 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d2440, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41073 p hg
    simpa only [d8142, d2440, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d2440, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d2440, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41075 (p : Pattern) (guard : d8143 p = 1) : d2441 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d2441, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41061 p hg
    simpa only [d8143, d2441, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d2441, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41074 p hg
    simpa only [d8143, d2441, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41076 (p : Pattern) (guard : d8144 p = 1) : d2442 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d2442, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40998 p hg
    simpa only [d8144, d2442, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d2442, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41075 p hg
    simpa only [d8144, d2442, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41077 (p : Pattern) (guard : d8145 p = 1) : d2443 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d2443, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40628 p hg
    simpa only [d8145, d2443, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d2443, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41076 p hg
    simpa only [d8145, d2443, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41078 (p : Pattern) (guard : d8085 p = 1) : d318 p ≤ (0 : Int) + d318 p := by
  omega
theorem compare41079 (p : Pattern) (guard : d8086 p = 1) : d2184 p ≤ (0 : Int) + d319 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2184, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34320 p hg
    simpa only [d8086, d2184, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2184, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41078 p hg
    simpa only [d8086, d2184, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41080 (p : Pattern) (guard : d8091 p = 1) : d2186 p ≤ (0 : Int) + d322 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2186, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41079 p hg
    simpa only [d8091, d2186, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2186, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40359 p hg
    simpa only [d8091, d2186, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41081 (p : Pattern) (guard : d8095 p = 1) : d2187 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2187, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40381 p hg
    simpa only [d8095, d2187, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2187, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2187, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41082 (p : Pattern) (guard : d8096 p = 1) : d2188 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2188, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41080 p hg
    simpa only [d8096, d2188, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2188, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41081 p hg
    simpa only [d8096, d2188, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41083 (p : Pattern) (guard : d8102 p = 1) : d2192 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2192, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41082 p hg
    simpa only [d8102, d2192, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2192, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40922 p hg
    simpa only [d8102, d2192, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41084 (p : Pattern) (guard : d8107 p = 1) : d2199 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2199, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40900 p hg
    simpa only [d8107, d2199, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2199, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40929 p hg
    simpa only [d8107, d2199, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41085 (p : Pattern) (guard : d8108 p = 1) : d2200 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2200, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41083 p hg
    simpa only [d8108, d2200, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2200, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41084 p hg
    simpa only [d8108, d2200, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41086 (p : Pattern) (guard : d8112 p = 1) : d2206 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2206, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40544 p hg
    simpa only [d8112, d2206, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2206, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2206, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41087 (p : Pattern) (guard : d8113 p = 1) : d2207 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2207, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40905 p hg
    simpa only [d8113, d2207, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2207, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41086 p hg
    simpa only [d8113, d2207, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41088 (p : Pattern) (guard : d8114 p = 1) : d2208 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2208, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41085 p hg
    simpa only [d8114, d2208, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2208, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41087 p hg
    simpa only [d8114, d2208, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41089 (p : Pattern) (guard : d8101 p = 1) : d2211 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2211, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40429 p hg
    simpa only [d8101, d2211, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2211, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40106 p hg
    simpa only [d8101, d2211, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41090 (p : Pattern) (guard : d8107 p = 1) : d2215 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2215, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41089 p hg
    simpa only [d8107, d2215, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2215, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40941 p hg
    simpa only [d8107, d2215, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41091 (p : Pattern) (guard : d8106 p = 1) : d2218 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2218, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40500 p hg
    simpa only [d8106, d2218, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2218, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40119 p hg
    simpa only [d8106, d2218, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41092 (p : Pattern) (guard : d8112 p = 1) : d2220 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2220, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41091 p hg
    simpa only [d8112, d2220, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2220, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40419 p hg
    simpa only [d8112, d2220, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41093 (p : Pattern) (guard : d8113 p = 1) : d2221 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2221, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41090 p hg
    simpa only [d8113, d2221, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2221, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41092 p hg
    simpa only [d8113, d2221, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41094 (p : Pattern) (guard : d8106 p = 1) : d2222 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2222, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40476 p hg
    simpa only [d8106, d2222, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2222, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2222, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41095 (p : Pattern) (guard : d8112 p = 1) : d2223 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2223, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41094 p hg
    simpa only [d8112, d2223, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2223, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40419 p hg
    simpa only [d8112, d2223, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41096 (p : Pattern) (guard : d8118 p = 1) : d2226 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2226, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41095 p hg
    simpa only [d8118, d2226, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2226, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40424 p hg
    simpa only [d8118, d2226, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41097 (p : Pattern) (guard : d8119 p = 1) : d2227 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2227, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41093 p hg
    simpa only [d8119, d2227, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2227, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41096 p hg
    simpa only [d8119, d2227, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41098 (p : Pattern) (guard : d8120 p = 1) : d2228 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2228, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41088 p hg
    simpa only [d8120, d2228, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2228, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41097 p hg
    simpa only [d8120, d2228, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41099 (p : Pattern) (guard : d8089 p = 1) : d357 p ≤ (0 : Int) + d357 p := by
  omega
theorem compare41100 (p : Pattern) (guard : d8090 p = 1) : d2229 p ≤ (0 : Int) + d381 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2229, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35583 p hg
    simpa only [d8090, d2229, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2229, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41099 p hg
    simpa only [d8090, d2229, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41101 (p : Pattern) (guard : d8095 p = 1) : d2230 p ≤ (0 : Int) + d382 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2230, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41100 p hg
    simpa only [d8095, d2230, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2230, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40499 p hg
    simpa only [d8095, d2230, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41102 (p : Pattern) (guard : d8100 p = 1) : d2187 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2187, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40618 p hg
    simpa only [d8100, d2187, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2187, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2187, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41103 (p : Pattern) (guard : d8101 p = 1) : d2231 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2231, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41101 p hg
    simpa only [d8101, d2231, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2231, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41102 p hg
    simpa only [d8101, d2231, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41104 (p : Pattern) (guard : d8094 p = 1) : d2209 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2209, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35589 p hg
    simpa only [d8094, d2209, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2209, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2209, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41105 (p : Pattern) (guard : d8100 p = 1) : d2209 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41104 p hg
    simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40211 p hg
    simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41106 (p : Pattern) (guard : d8106 p = 1) : d2232 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2232, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41105 p hg
    simpa only [d8106, d2232, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2232, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40256 p hg
    simpa only [d8106, d2232, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41107 (p : Pattern) (guard : d8107 p = 1) : d2233 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2233, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41103 p hg
    simpa only [d8107, d2233, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2233, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41106 p hg
    simpa only [d8107, d2233, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41108 (p : Pattern) (guard : d8094 p = 1) : d2196 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2196, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35595 p hg
    simpa only [d8094, d2196, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2196, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2196, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41109 (p : Pattern) (guard : d8100 p = 1) : d2196 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41108 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40182 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41110 (p : Pattern) (guard : d8106 p = 1) : d2198 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2198, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41109 p hg
    simpa only [d8106, d2198, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2198, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40236 p hg
    simpa only [d8106, d2198, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41111 (p : Pattern) (guard : d8099 p = 1) : d2203 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2203, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35599 p hg
    simpa only [d8099, d2203, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2203, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2203, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41112 (p : Pattern) (guard : d8105 p = 1) : d2203 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41111 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40215 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41113 (p : Pattern) (guard : d8111 p = 1) : d2205 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2205, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41112 p hg
    simpa only [d8111, d2205, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2205, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40259 p hg
    simpa only [d8111, d2205, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41114 (p : Pattern) (guard : d8112 p = 1) : d2234 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2234, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41110 p hg
    simpa only [d8112, d2234, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2234, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41113 p hg
    simpa only [d8112, d2234, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41115 (p : Pattern) (guard : d8113 p = 1) : d2235 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2235, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41107 p hg
    simpa only [d8113, d2235, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2235, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41114 p hg
    simpa only [d8113, d2235, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41116 (p : Pattern) (guard : d8112 p = 1) : d2239 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2239, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40929 p hg
    simpa only [d8112, d2239, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2239, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40707 p hg
    simpa only [d8112, d2239, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41117 (p : Pattern) (guard : d8117 p = 1) : d2241 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2241, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40712 p hg
    simpa only [d8117, d2241, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2241, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2241, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41118 (p : Pattern) (guard : d8118 p = 1) : d2242 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2242, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41116 p hg
    simpa only [d8118, d2242, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2242, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41117 p hg
    simpa only [d8118, d2242, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41119 (p : Pattern) (guard : d8119 p = 1) : d2243 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2243, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41115 p hg
    simpa only [d8119, d2243, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2243, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41118 p hg
    simpa only [d8119, d2243, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41120 (p : Pattern) (guard : d8106 p = 1) : d2214 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2214, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40954 p hg
    simpa only [d8106, d2214, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2214, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40247 p hg
    simpa only [d8106, d2214, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41121 (p : Pattern) (guard : d8111 p = 1) : d2244 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2244, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40957 p hg
    simpa only [d8111, d2244, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2244, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2244, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41122 (p : Pattern) (guard : d8112 p = 1) : d2245 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2245, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41120 p hg
    simpa only [d8112, d2245, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2245, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41121 p hg
    simpa only [d8112, d2245, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41123 (p : Pattern) (guard : d8118 p = 1) : d2247 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2247, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41122 p hg
    simpa only [d8118, d2247, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2247, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40448 p hg
    simpa only [d8118, d2247, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41124 (p : Pattern) (guard : d8124 p = 1) : d2253 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2253, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41123 p hg
    simpa only [d8124, d2253, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2253, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40453 p hg
    simpa only [d8124, d2253, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41125 (p : Pattern) (guard : d8125 p = 1) : d2254 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2254, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41119 p hg
    simpa only [d8125, d2254, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2254, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41124 p hg
    simpa only [d8125, d2254, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41126 (p : Pattern) (guard : d8126 p = 1) : d2255 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2255, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41098 p hg
    simpa only [d8126, d2255, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2255, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41125 p hg
    simpa only [d8126, d2255, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41127 (p : Pattern) (guard : d8132 p = 1) : d2271 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d2271, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41126 p hg
    simpa only [d8132, d2271, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d2271, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40988 p hg
    simpa only [d8132, d2271, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41128 (p : Pattern) (guard : d8112 p = 1) : d2259 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2259, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40386 p hg
    simpa only [d8112, d2259, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2259, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40470 p hg
    simpa only [d8112, d2259, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41129 (p : Pattern) (guard : d8118 p = 1) : d2260 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2260, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41128 p hg
    simpa only [d8118, d2260, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2260, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40268 p hg
    simpa only [d8118, d2260, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41130 (p : Pattern) (guard : d8124 p = 1) : d2261 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2261, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41129 p hg
    simpa only [d8124, d2261, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2261, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d2261, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41131 (p : Pattern) (guard : d8125 p = 1) : d2275 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2275, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41003 p hg
    simpa only [d8125, d2275, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2275, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41130 p hg
    simpa only [d8125, d2275, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41132 (p : Pattern) (guard : d8130 p = 1) : d2269 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2269, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41028 p hg
    simpa only [d8130, d2269, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2269, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40491 p hg
    simpa only [d8130, d2269, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41133 (p : Pattern) (guard : d8131 p = 1) : d2276 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2276, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41131 p hg
    simpa only [d8131, d2276, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2276, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41132 p hg
    simpa only [d8131, d2276, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41134 (p : Pattern) (guard : d8112 p = 1) : d2277 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2277, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40544 p hg
    simpa only [d8112, d2277, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2277, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40267 p hg
    simpa only [d8112, d2277, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41135 (p : Pattern) (guard : d8118 p = 1) : d2278 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2278, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41134 p hg
    simpa only [d8118, d2278, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2278, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40268 p hg
    simpa only [d8118, d2278, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41136 (p : Pattern) (guard : d8124 p = 1) : d2280 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2280, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41135 p hg
    simpa only [d8124, d2280, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2280, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40991 p hg
    simpa only [d8124, d2280, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41137 (p : Pattern) (guard : d8130 p = 1) : d2282 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2282, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41136 p hg
    simpa only [d8130, d2282, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2282, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40993 p hg
    simpa only [d8130, d2282, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41138 (p : Pattern) (guard : d8123 p = 1) : d2279 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2279, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41117 p hg
    simpa only [d8123, d2279, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2279, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2279, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41139 (p : Pattern) (guard : d8129 p = 1) : d2281 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2281, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41138 p hg
    simpa only [d8129, d2281, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2281, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d2281, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41140 (p : Pattern) (guard : d8135 p = 1) : d2283 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2283, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41139 p hg
    simpa only [d8135, d2283, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2283, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d2283, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41141 (p : Pattern) (guard : d8136 p = 1) : d2284 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2284, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41137 p hg
    simpa only [d8136, d2284, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2284, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41140 p hg
    simpa only [d8136, d2284, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41142 (p : Pattern) (guard : d8137 p = 1) : d2285 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2285, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41133 p hg
    simpa only [d8137, d2285, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2285, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41141 p hg
    simpa only [d8137, d2285, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41143 (p : Pattern) (guard : d8138 p = 1) : d2286 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d2286, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41127 p hg
    simpa only [d8138, d2286, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d2286, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41142 p hg
    simpa only [d8138, d2286, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41144 (p : Pattern) (guard : d8107 p = 1) : d2287 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2287, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40922 p hg
    simpa only [d8107, d2287, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2287, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41016 p hg
    simpa only [d8107, d2287, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41145 (p : Pattern) (guard : d8112 p = 1) : d2202 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2202, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40976 p hg
    simpa only [d8112, d2202, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2202, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41023 p hg
    simpa only [d8112, d2202, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41146 (p : Pattern) (guard : d8113 p = 1) : d2288 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2288, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41144 p hg
    simpa only [d8113, d2288, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2288, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41145 p hg
    simpa only [d8113, d2288, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41147 (p : Pattern) (guard : d8118 p = 1) : d2207 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2207, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41000 p hg
    simpa only [d8118, d2207, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2207, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40464 p hg
    simpa only [d8118, d2207, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41148 (p : Pattern) (guard : d8119 p = 1) : d2289 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2289, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41146 p hg
    simpa only [d8119, d2289, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2289, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41147 p hg
    simpa only [d8119, d2289, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41149 (p : Pattern) (guard : d8106 p = 1) : d2211 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2211, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40619 p hg
    simpa only [d8106, d2211, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2211, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40256 p hg
    simpa only [d8106, d2211, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41150 (p : Pattern) (guard : d8111 p = 1) : d2214 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41038 p hg
    simpa only [d8111, d2214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40469 p hg
    simpa only [d8111, d2214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41151 (p : Pattern) (guard : d8112 p = 1) : d2215 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2215, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41149 p hg
    simpa only [d8112, d2215, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2215, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41150 p hg
    simpa only [d8112, d2215, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41152 (p : Pattern) (guard : d8111 p = 1) : d2218 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41038 p hg
    simpa only [d8111, d2218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40266 p hg
    simpa only [d8111, d2218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41153 (p : Pattern) (guard : d8117 p = 1) : d2220 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41152 p hg
    simpa only [d8117, d2220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41029 p hg
    simpa only [d8117, d2220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41154 (p : Pattern) (guard : d8118 p = 1) : d2221 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2221, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41151 p hg
    simpa only [d8118, d2221, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2221, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41153 p hg
    simpa only [d8118, d2221, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41155 (p : Pattern) (guard : d8111 p = 1) : d2222 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41038 p hg
    simpa only [d8111, d2222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41156 (p : Pattern) (guard : d8117 p = 1) : d2223 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41155 p hg
    simpa only [d8117, d2223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41029 p hg
    simpa only [d8117, d2223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41157 (p : Pattern) (guard : d0 p = 1) : d2225 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41158 (p : Pattern) (guard : d8123 p = 1) : d2226 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41156 p hg
    simpa only [d8123, d2226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41157 p hg
    simpa only [d8123, d2226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41159 (p : Pattern) (guard : d8124 p = 1) : d2227 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2227, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41154 p hg
    simpa only [d8124, d2227, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2227, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41158 p hg
    simpa only [d8124, d2227, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
