/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons058
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare8260 (p : Pattern) (guard : d1294 p = 1) : d726 p ≤ (0 : Int) + d108 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d726, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8252 p hg
    simpa only [d726, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d726, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8259 p hg
    simpa only [d726, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8261 (p : Pattern) (guard : d1294 p = 1) : d705 p ≤ (0 : Int) + d97 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7746 p hg
    simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8248 p hg
    simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8262 (p : Pattern) (guard : d1294 p = 1) : d705 p ≤ (0 : Int) + d109 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7746 p hg
    simpa only [d1294, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8221 p hg
    simpa only [d1294, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8263 (p : Pattern) (guard : d1294 p = 1) : d705 p ≤ (0 : Int) + d110 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8261 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8262 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8264 (p : Pattern) (guard : d1294 p = 1) : d727 p ≤ (0 : Int) + d111 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d727, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8262 p hg
    simpa only [d727, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d727, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4572 p hg
    simpa only [d727, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8265 (p : Pattern) (guard : d1294 p = 1) : d728 p ≤ (0 : Int) + d112 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d728, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8263 p hg
    simpa only [d728, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d728, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8264 p hg
    simpa only [d728, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8266 (p : Pattern) (guard : d1294 p = 1) : d729 p ≤ (0 : Int) + d113 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d729, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8260 p hg
    simpa only [d729, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d729, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8265 p hg
    simpa only [d729, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8267 (p : Pattern) (guard : d1294 p = 1) : d730 p ≤ (0 : Int) + d114 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d730, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8258 p hg
    simpa only [d730, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d730, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8266 p hg
    simpa only [d730, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8268 (p : Pattern) (guard : d1294 p = 1) : d731 p ≤ (0 : Int) + d115 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d731, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8255 p hg
    simpa only [d731, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d731, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8267 p hg
    simpa only [d731, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8269 (p : Pattern) (guard : d1294 p = 1) : d732 p ≤ (0 : Int) + d116 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d732, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8236 p hg
    simpa only [d732, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d732, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8268 p hg
    simpa only [d732, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8270 (p : Pattern) (guard : d1294 p = 1) : d733 p ≤ (0 : Int) + d117 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d733, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8228 p hg
    simpa only [d733, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d733, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8234 p hg
    simpa only [d733, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8271 (p : Pattern) (guard : d1294 p = 1) : d734 p ≤ (0 : Int) + d118 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d734, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8220 p hg
    simpa only [d734, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d734, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8270 p hg
    simpa only [d734, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8272 (p : Pattern) (guard : d1293 p = 1) : d697 p ≤ (0 : Int) + d119 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8192 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8180 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8273 (p : Pattern) (guard : d1293 p = 1) : d719 p ≤ (0 : Int) + d120 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d719, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8272 p hg
    simpa only [d719, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d719, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8213 p hg
    simpa only [d719, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8274 (p : Pattern) (guard : d1294 p = 1) : d719 p ≤ (0 : Int) + d121 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7738 p hg
    simpa only [d1294, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8273 p hg
    simpa only [d1294, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8275 (p : Pattern) (guard : d1294 p = 1) : d719 p ≤ (0 : Int) + d122 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8274 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8244 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8276 (p : Pattern) (guard : d1294 p = 1) : d719 p ≤ (0 : Int) + d123 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8241 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8275 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8277 (p : Pattern) (guard : d1294 p = 1) : d720 p ≤ (0 : Int) + d124 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d720, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8198 p hg
    simpa only [d720, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d720, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8276 p hg
    simpa only [d720, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8278 (p : Pattern) (guard : d1294 p = 1) : d705 p ≤ (0 : Int) + d125 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8262 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8226 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8279 (p : Pattern) (guard : d1294 p = 1) : d705 p ≤ (0 : Int) + d126 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8263 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8278 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8280 (p : Pattern) (guard : d1294 p = 1) : d735 p ≤ (0 : Int) + d127 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d735, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8254 p hg
    simpa only [d735, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d735, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8279 p hg
    simpa only [d735, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8281 (p : Pattern) (guard : d1294 p = 1) : d736 p ≤ (0 : Int) + d128 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d736, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8277 p hg
    simpa only [d736, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d736, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8280 p hg
    simpa only [d736, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8282 (p : Pattern) (guard : d1294 p = 1) : d737 p ≤ (0 : Int) + d129 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d737, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8228 p hg
    simpa only [d737, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d737, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8233 p hg
    simpa only [d737, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8283 (p : Pattern) (guard : d1294 p = 1) : d738 p ≤ (0 : Int) + d130 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d738, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8265 p hg
    simpa only [d738, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d738, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4572 p hg
    simpa only [d738, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8284 (p : Pattern) (guard : d1294 p = 1) : d739 p ≤ (0 : Int) + d131 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d739, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8282 p hg
    simpa only [d739, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d739, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8283 p hg
    simpa only [d739, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8285 (p : Pattern) (guard : d1294 p = 1) : d740 p ≤ (0 : Int) + d132 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d740, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8281 p hg
    simpa only [d740, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d740, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8284 p hg
    simpa only [d740, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8286 (p : Pattern) (guard : d1294 p = 1) : d741 p ≤ (0 : Int) + d133 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d741, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8271 p hg
    simpa only [d741, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d741, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8285 p hg
    simpa only [d741, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8287 (p : Pattern) (guard : d1294 p = 1) : d742 p ≤ (0 : Int) + d134 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d742, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8269 p hg
    simpa only [d742, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d742, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8286 p hg
    simpa only [d742, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8288 (p : Pattern) (guard : d1240 p = 1) : d5 p ≤ (0 : Int) + d6 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1240, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4109 p hg
    simpa only [d1240, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1240, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3418 p hg
    simpa only [d1240, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8289 (p : Pattern) (guard : d1240 p = 1) : d697 p ≤ (0 : Int) + d8 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d697, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8288 p hg
    simpa only [d697, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d697, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4110 p hg
    simpa only [d697, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8290 (p : Pattern) (guard : d1240 p = 1) : d11 p ≤ (0 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1240, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4112 p hg
    simpa only [d1240, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1240, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3422 p hg
    simpa only [d1240, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8291 (p : Pattern) (guard : d1240 p = 1) : d698 p ≤ (0 : Int) + d14 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d698, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8290 p hg
    simpa only [d698, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d698, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4113 p hg
    simpa only [d698, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8292 (p : Pattern) (guard : d1240 p = 1) : d699 p ≤ (0 : Int) + d15 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d699, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8289 p hg
    simpa only [d699, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d699, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8291 p hg
    simpa only [d699, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8293 (p : Pattern) (guard : d1240 p = 1) : d700 p ≤ (0 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d700, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8289 p hg
    simpa only [d700, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d700, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8292 p hg
    simpa only [d700, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8294 (p : Pattern) (guard : d1241 p = 1) : d700 p ≤ (0 : Int) + d16 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7694 p hg
    simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8293 p hg
    simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8295 (p : Pattern) (guard : d0 p = 1) : d700 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8296 (p : Pattern) (guard : d1242 p = 1) : d700 p ≤ (0 : Int) + d293 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8294 p hg
    simpa only [d1242, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8295 p hg
    simpa only [d1242, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8297 (p : Pattern) (guard : d1241 p = 1) : d699 p ≤ (0 : Int) + d15 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7693 p hg
    simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8292 p hg
    simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8298 (p : Pattern) (guard : d1242 p = 1) : d699 p ≤ (0 : Int) + d294 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8297 p hg
    simpa only [d1242, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7704 p hg
    simpa only [d1242, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8299 (p : Pattern) (guard : d1240 p = 1) : d701 p ≤ (0 : Int) + d52 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d701, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8289 p hg
    simpa only [d701, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d701, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3436 p hg
    simpa only [d701, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8300 (p : Pattern) (guard : d1240 p = 1) : d702 p ≤ (0 : Int) + d53 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d702, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8292 p hg
    simpa only [d702, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d702, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8299 p hg
    simpa only [d702, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8301 (p : Pattern) (guard : d1241 p = 1) : d702 p ≤ (0 : Int) + d53 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7710 p hg
    simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8300 p hg
    simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8302 (p : Pattern) (guard : d1242 p = 1) : d702 p ≤ (0 : Int) + d295 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8301 p hg
    simpa only [d1242, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7711 p hg
    simpa only [d1242, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8303 (p : Pattern) (guard : d1242 p = 1) : d703 p ≤ (0 : Int) + d296 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d703, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8298 p hg
    simpa only [d703, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d703, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8302 p hg
    simpa only [d703, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8304 (p : Pattern) (guard : d1242 p = 1) : d704 p ≤ (0 : Int) + d297 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d704, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8296 p hg
    simpa only [d704, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d704, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8303 p hg
    simpa only [d704, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8305 (p : Pattern) (guard : d0 p = 1) : d706 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8306 (p : Pattern) (guard : d1242 p = 1) : d707 p ≤ (0 : Int) + d293 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d707, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8294 p hg
    simpa only [d1242, d707, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d707, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8305 p hg
    simpa only [d1242, d707, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8307 (p : Pattern) (guard : d1242 p = 1) : d708 p ≤ (0 : Int) + d293 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8296 p hg
    simpa only [d708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8306 p hg
    simpa only [d708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8308 (p : Pattern) (guard : d0 p = 1) : d705 p ≤ (0 : Int) + d148 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8309 (p : Pattern) (guard : d1242 p = 1) : d709 p ≤ (0 : Int) + d298 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d709, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8294 p hg
    simpa only [d1242, d709, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d709, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8308 p hg
    simpa only [d1242, d709, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8310 (p : Pattern) (guard : d1242 p = 1) : d710 p ≤ (0 : Int) + d299 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d710, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8296 p hg
    simpa only [d710, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d710, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8309 p hg
    simpa only [d710, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8311 (p : Pattern) (guard : d1242 p = 1) : d711 p ≤ (0 : Int) + d300 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d711, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8307 p hg
    simpa only [d711, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d711, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8310 p hg
    simpa only [d711, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8312 (p : Pattern) (guard : d1242 p = 1) : d712 p ≤ (0 : Int) + d294 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d712, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8297 p hg
    simpa only [d1242, d712, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d712, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7726 p hg
    simpa only [d1242, d712, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8313 (p : Pattern) (guard : d1242 p = 1) : d713 p ≤ (0 : Int) + d294 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8298 p hg
    simpa only [d713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8312 p hg
    simpa only [d713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8314 (p : Pattern) (guard : d1242 p = 1) : d714 p ≤ (0 : Int) + d295 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d714, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8301 p hg
    simpa only [d1242, d714, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d714, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7726 p hg
    simpa only [d1242, d714, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8315 (p : Pattern) (guard : d1242 p = 1) : d715 p ≤ (0 : Int) + d295 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8302 p hg
    simpa only [d715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8314 p hg
    simpa only [d715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8316 (p : Pattern) (guard : d1242 p = 1) : d716 p ≤ (0 : Int) + d296 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d716, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8313 p hg
    simpa only [d716, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d716, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8315 p hg
    simpa only [d716, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8317 (p : Pattern) (guard : d1242 p = 1) : d717 p ≤ (0 : Int) + d301 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d717, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8311 p hg
    simpa only [d717, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d717, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8316 p hg
    simpa only [d717, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8318 (p : Pattern) (guard : d1242 p = 1) : d718 p ≤ (0 : Int) + d302 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d718, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8304 p hg
    simpa only [d718, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d718, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8317 p hg
    simpa only [d718, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8319 (p : Pattern) (guard : d1240 p = 1) : d719 p ≤ (0 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d719, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8289 p hg
    simpa only [d719, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d719, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8299 p hg
    simpa only [d719, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8320 (p : Pattern) (guard : d1241 p = 1) : d719 p ≤ (0 : Int) + d86 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7738 p hg
    simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8319 p hg
    simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8321 (p : Pattern) (guard : d0 p = 1) : d719 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8322 (p : Pattern) (guard : d1242 p = 1) : d719 p ≤ (0 : Int) + d303 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8320 p hg
    simpa only [d1242, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8321 p hg
    simpa only [d1242, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8323 (p : Pattern) (guard : d0 p = 1) : d719 p ≤ (0 : Int) + d148 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8324 (p : Pattern) (guard : d1242 p = 1) : d719 p ≤ (0 : Int) + d304 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8320 p hg
    simpa only [d1242, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8323 p hg
    simpa only [d1242, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8325 (p : Pattern) (guard : d1242 p = 1) : d719 p ≤ (0 : Int) + d305 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8322 p hg
    simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8324 p hg
    simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8326 (p : Pattern) (guard : d1242 p = 1) : d720 p ≤ (0 : Int) + d306 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d720, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8296 p hg
    simpa only [d720, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d720, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8325 p hg
    simpa only [d720, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8327 (p : Pattern) (guard : d1240 p = 1) : d705 p ≤ (0 : Int) + d97 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d705, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8291 p hg
    simpa only [d705, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d705, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3436 p hg
    simpa only [d705, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8328 (p : Pattern) (guard : d1240 p = 1) : d706 p ≤ (0 : Int) + d98 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d706, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8291 p hg
    simpa only [d706, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d706, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8327 p hg
    simpa only [d706, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8329 (p : Pattern) (guard : d1241 p = 1) : d706 p ≤ (0 : Int) + d98 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7747 p hg
    simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8328 p hg
    simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8330 (p : Pattern) (guard : d1242 p = 1) : d706 p ≤ (0 : Int) + d307 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8329 p hg
    simpa only [d1242, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7722 p hg
    simpa only [d1242, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8331 (p : Pattern) (guard : d1242 p = 1) : d721 p ≤ (0 : Int) + d308 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d721, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8326 p hg
    simpa only [d721, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d721, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8330 p hg
    simpa only [d721, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8332 (p : Pattern) (guard : d1242 p = 1) : d722 p ≤ (0 : Int) + d309 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d722, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8320 p hg
    simpa only [d1242, d722, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d722, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7726 p hg
    simpa only [d1242, d722, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8333 (p : Pattern) (guard : d1242 p = 1) : d723 p ≤ (0 : Int) + d310 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d723, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8324 p hg
    simpa only [d723, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d723, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8332 p hg
    simpa only [d723, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8334 (p : Pattern) (guard : d1242 p = 1) : d724 p ≤ (0 : Int) + d311 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d724, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8310 p hg
    simpa only [d724, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d724, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8333 p hg
    simpa only [d724, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8335 (p : Pattern) (guard : d1242 p = 1) : d725 p ≤ (0 : Int) + d307 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d725, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8329 p hg
    simpa only [d1242, d725, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d725, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1242, d725, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8336 (p : Pattern) (guard : d1242 p = 1) : d726 p ≤ (0 : Int) + d307 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8330 p hg
    simpa only [d726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8335 p hg
    simpa only [d726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8337 (p : Pattern) (guard : d1241 p = 1) : d705 p ≤ (0 : Int) + d97 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7746 p hg
    simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8327 p hg
    simpa only [d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8338 (p : Pattern) (guard : d1242 p = 1) : d705 p ≤ (0 : Int) + d312 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8337 p hg
    simpa only [d1242, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7726 p hg
    simpa only [d1242, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8339 (p : Pattern) (guard : d1242 p = 1) : d727 p ≤ (0 : Int) + d312 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d727, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8337 p hg
    simpa only [d1242, d727, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d727, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1242, d727, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8340 (p : Pattern) (guard : d1242 p = 1) : d728 p ≤ (0 : Int) + d312 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8338 p hg
    simpa only [d728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8339 p hg
    simpa only [d728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8341 (p : Pattern) (guard : d1242 p = 1) : d729 p ≤ (0 : Int) + d313 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d729, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8336 p hg
    simpa only [d729, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d729, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8340 p hg
    simpa only [d729, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8342 (p : Pattern) (guard : d1242 p = 1) : d730 p ≤ (0 : Int) + d314 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d730, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8334 p hg
    simpa only [d730, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d730, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8341 p hg
    simpa only [d730, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8343 (p : Pattern) (guard : d1242 p = 1) : d731 p ≤ (0 : Int) + d315 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d731, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8331 p hg
    simpa only [d731, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d731, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8342 p hg
    simpa only [d731, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8344 (p : Pattern) (guard : d1242 p = 1) : d732 p ≤ (0 : Int) + d316 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d732, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8318 p hg
    simpa only [d732, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d732, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8343 p hg
    simpa only [d732, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8345 (p : Pattern) (guard : d0 p = 1) : d700 p ≤ (0 : Int) + d148 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8346 (p : Pattern) (guard : d1242 p = 1) : d700 p ≤ (0 : Int) + d298 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8294 p hg
    simpa only [d1242, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8345 p hg
    simpa only [d1242, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8347 (p : Pattern) (guard : d1242 p = 1) : d700 p ≤ (0 : Int) + d299 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8296 p hg
    simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8346 p hg
    simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8348 (p : Pattern) (guard : d1242 p = 1) : d700 p ≤ (0 : Int) + d300 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8296 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8347 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8349 (p : Pattern) (guard : d1242 p = 1) : d704 p ≤ (0 : Int) + d301 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d704, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8348 p hg
    simpa only [d704, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d704, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8303 p hg
    simpa only [d704, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8350 (p : Pattern) (guard : d1242 p = 1) : d709 p ≤ (0 : Int) + d317 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d709, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8294 p hg
    simpa only [d1242, d709, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d709, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7726 p hg
    simpa only [d1242, d709, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8351 (p : Pattern) (guard : d1242 p = 1) : d710 p ≤ (0 : Int) + d318 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d710, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8346 p hg
    simpa only [d710, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d710, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8350 p hg
    simpa only [d710, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8352 (p : Pattern) (guard : d1242 p = 1) : d710 p ≤ (0 : Int) + d319 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8310 p hg
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8351 p hg
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8353 (p : Pattern) (guard : d1242 p = 1) : d733 p ≤ (0 : Int) + d320 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d733, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8352 p hg
    simpa only [d733, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d733, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8316 p hg
    simpa only [d733, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8354 (p : Pattern) (guard : d1242 p = 1) : d734 p ≤ (0 : Int) + d321 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d734, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8349 p hg
    simpa only [d734, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d734, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8353 p hg
    simpa only [d734, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8355 (p : Pattern) (guard : d1242 p = 1) : d719 p ≤ (0 : Int) + d309 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1241 p = 1 := by simpa only [d1242, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8320 p hg
    simpa only [d1242, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1242, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7739 p hg
    simpa only [d1242, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8356 (p : Pattern) (guard : d1242 p = 1) : d719 p ≤ (0 : Int) + d310 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8324 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8355 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8357 (p : Pattern) (guard : d1242 p = 1) : d720 p ≤ (0 : Int) + d311 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d720, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8347 p hg
    simpa only [d720, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d720, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8356 p hg
    simpa only [d720, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8358 (p : Pattern) (guard : d1242 p = 1) : d735 p ≤ (0 : Int) + d313 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d735, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8330 p hg
    simpa only [d735, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d735, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8338 p hg
    simpa only [d735, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8359 (p : Pattern) (guard : d1242 p = 1) : d736 p ≤ (0 : Int) + d314 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d736, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8357 p hg
    simpa only [d736, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d736, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8358 p hg
    simpa only [d736, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8360 (p : Pattern) (guard : d1242 p = 1) : d737 p ≤ (0 : Int) + d322 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d737, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8351 p hg
    simpa only [d737, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d737, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8315 p hg
    simpa only [d737, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8361 (p : Pattern) (guard : d1242 p = 1) : d738 p ≤ (0 : Int) + d323 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d738, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8340 p hg
    simpa only [d738, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d738, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3506 p hg
    simpa only [d738, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8362 (p : Pattern) (guard : d1242 p = 1) : d739 p ≤ (0 : Int) + d324 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d739, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8360 p hg
    simpa only [d739, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d739, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8361 p hg
    simpa only [d739, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8363 (p : Pattern) (guard : d1242 p = 1) : d740 p ≤ (0 : Int) + d325 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d740, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8359 p hg
    simpa only [d740, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d740, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8362 p hg
    simpa only [d740, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8364 (p : Pattern) (guard : d1242 p = 1) : d741 p ≤ (0 : Int) + d326 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d741, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8354 p hg
    simpa only [d741, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d741, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8363 p hg
    simpa only [d741, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8365 (p : Pattern) (guard : d1242 p = 1) : d742 p ≤ (0 : Int) + d327 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1242 p = 1 := by simpa only [d742, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8344 p hg
    simpa only [d742, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1242 p = 1 := by simpa only [d742, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8364 p hg
    simpa only [d742, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8366 (p : Pattern) (guard : d985 p = 1) : d3 p ≤ (0 : Int) + d4 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d4, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3977 p hg
    simpa only [d4, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8367 (p : Pattern) (guard : d985 p = 1) : d17 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d17, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d17, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d17, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d17, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8368 (p : Pattern) (guard : d985 p = 1) : d743 p ≤ (0 : Int) + d6 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d743, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8366 p hg
    simpa only [d743, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d743, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8367 p hg
    simpa only [d743, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8369 (p : Pattern) (guard : d985 p = 1) : d744 p ≤ (0 : Int) + d7 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d744, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8366 p hg
    simpa only [d744, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d744, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d744, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8370 (p : Pattern) (guard : d985 p = 1) : d745 p ≤ (0 : Int) + d8 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d745, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8368 p hg
    simpa only [d745, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d745, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8369 p hg
    simpa only [d745, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8371 (p : Pattern) (guard : d985 p = 1) : d9 p ≤ (0 : Int) + d10 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4491 p hg
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3985 p hg
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8372 (p : Pattern) (guard : d985 p = 1) : d21 p ≤ (0 : Int) + d11 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d21, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4491 p hg
    simpa only [d21, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d21, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d21, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8373 (p : Pattern) (guard : d985 p = 1) : d746 p ≤ (0 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d746, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8371 p hg
    simpa only [d746, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d746, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8372 p hg
    simpa only [d746, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8374 (p : Pattern) (guard : d985 p = 1) : d747 p ≤ (0 : Int) + d13 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d747, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8371 p hg
    simpa only [d747, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d747, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d747, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8375 (p : Pattern) (guard : d985 p = 1) : d748 p ≤ (0 : Int) + d14 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d748, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8373 p hg
    simpa only [d748, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d748, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8374 p hg
    simpa only [d748, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8376 (p : Pattern) (guard : d985 p = 1) : d749 p ≤ (0 : Int) + d15 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d749, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8370 p hg
    simpa only [d749, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d749, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8375 p hg
    simpa only [d749, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8377 (p : Pattern) (guard : d985 p = 1) : d750 p ≤ (0 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d750, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8370 p hg
    simpa only [d750, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d750, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8376 p hg
    simpa only [d750, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8378 (p : Pattern) (guard : d985 p = 1) : d743 p ≤ (0 : Int) + d18 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d743, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8366 p hg
    simpa only [d743, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d743, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4199 p hg
    simpa only [d743, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8379 (p : Pattern) (guard : d985 p = 1) : d751 p ≤ (0 : Int) + d20 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d751, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8378 p hg
    simpa only [d751, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d751, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4201 p hg
    simpa only [d751, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8380 (p : Pattern) (guard : d985 p = 1) : d746 p ≤ (0 : Int) + d22 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d746, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8371 p hg
    simpa only [d746, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d746, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4203 p hg
    simpa only [d746, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8381 (p : Pattern) (guard : d985 p = 1) : d752 p ≤ (0 : Int) + d24 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d752, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8380 p hg
    simpa only [d752, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d752, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4205 p hg
    simpa only [d752, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8382 (p : Pattern) (guard : d985 p = 1) : d753 p ≤ (0 : Int) + d25 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d753, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8379 p hg
    simpa only [d753, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d753, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8381 p hg
    simpa only [d753, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8383 (p : Pattern) (guard : d985 p = 1) : d754 p ≤ (0 : Int) + d26 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d754, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8379 p hg
    simpa only [d754, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d754, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8382 p hg
    simpa only [d754, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8384 (p : Pattern) (guard : d985 p = 1) : d755 p ≤ (0 : Int) + d27 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d755, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8377 p hg
    simpa only [d755, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d755, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8383 p hg
    simpa only [d755, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8385 (p : Pattern) (guard : d985 p = 1) : d756 p ≤ (0 : Int) + d28 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d756, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8377 p hg
    simpa only [d756, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d756, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8384 p hg
    simpa only [d756, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8386 (p : Pattern) (guard : d985 p = 1) : d3 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d985, d3, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare103 p hg
    simpa only [d985, d3, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d985, d3, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4490 p hg
    simpa only [d985, d3, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8387 (p : Pattern) (guard : d985 p = 1) : d17 p ≤ (0 : Int) + d30 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d17, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8386 p hg
    simpa only [d17, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d17, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d17, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8388 (p : Pattern) (guard : d985 p = 1) : d743 p ≤ (0 : Int) + d31 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d743, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8366 p hg
    simpa only [d743, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d743, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8387 p hg
    simpa only [d743, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8389 (p : Pattern) (guard : d985 p = 1) : d19 p ≤ (0 : Int) + d32 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d19, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8387 p hg
    simpa only [d19, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d19, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d19, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8390 (p : Pattern) (guard : d985 p = 1) : d751 p ≤ (0 : Int) + d33 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d751, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8388 p hg
    simpa only [d751, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d751, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8389 p hg
    simpa only [d751, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8391 (p : Pattern) (guard : d985 p = 1) : d753 p ≤ (0 : Int) + d34 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d753, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8390 p hg
    simpa only [d753, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d753, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8381 p hg
    simpa only [d753, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8392 (p : Pattern) (guard : d985 p = 1) : d754 p ≤ (0 : Int) + d35 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d754, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8390 p hg
    simpa only [d754, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d754, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8391 p hg
    simpa only [d754, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8393 (p : Pattern) (guard : d985 p = 1) : d755 p ≤ (0 : Int) + d36 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d755, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8377 p hg
    simpa only [d755, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d755, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8392 p hg
    simpa only [d755, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8394 (p : Pattern) (guard : d985 p = 1) : d19 p ≤ (0 : Int) + d37 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d19, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8367 p hg
    simpa only [d19, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d19, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d19, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8395 (p : Pattern) (guard : d985 p = 1) : d751 p ≤ (0 : Int) + d38 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d751, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8368 p hg
    simpa only [d751, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d751, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8394 p hg
    simpa only [d751, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8396 (p : Pattern) (guard : d985 p = 1) : d23 p ≤ (0 : Int) + d39 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8372 p hg
    simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8397 (p : Pattern) (guard : d985 p = 1) : d752 p ≤ (0 : Int) + d40 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d752, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8373 p hg
    simpa only [d752, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d752, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8396 p hg
    simpa only [d752, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8398 (p : Pattern) (guard : d985 p = 1) : d753 p ≤ (0 : Int) + d41 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d753, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8395 p hg
    simpa only [d753, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d753, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8397 p hg
    simpa only [d753, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8399 (p : Pattern) (guard : d985 p = 1) : d754 p ≤ (0 : Int) + d42 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d754, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8395 p hg
    simpa only [d754, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d754, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8398 p hg
    simpa only [d754, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
