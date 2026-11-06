/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons344
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare48300 (p : Pattern) (guard : d8136 p = 1) : d472 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d472, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48299 p hg
    simpa only [d8136, d472, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d472, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38317 p hg
    simpa only [d8136, d472, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48301 (p : Pattern) (guard : d8142 p = 1) : d474 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d474, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48300 p hg
    simpa only [d8142, d474, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d474, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41761 p hg
    simpa only [d8142, d474, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48302 (p : Pattern) (guard : d8148 p = 1) : d477 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8142 p = 1 := by simpa only [d8148, d477, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48301 p hg
    simpa only [d8148, d477, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8147 p = 1 := by simpa only [d8148, d477, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35861 p hg
    simpa only [d8148, d477, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48303 (p : Pattern) (guard : d8149 p = 1) : d478 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8143 p = 1 := by simpa only [d8149, d478, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48294 p hg
    simpa only [d8149, d478, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8148 p = 1 := by simpa only [d8149, d478, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48302 p hg
    simpa only [d8149, d478, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48304 (p : Pattern) (guard : d8150 p = 1) : d479 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8144 p = 1 := by simpa only [d8150, d479, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48290 p hg
    simpa only [d8150, d479, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8149 p = 1 := by simpa only [d8150, d479, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48303 p hg
    simpa only [d8150, d479, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48305 (p : Pattern) (guard : d8151 p = 1) : d480 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8145 p = 1 := by simpa only [d8151, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48289 p hg
    simpa only [d8151, d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8150 p = 1 := by simpa only [d8151, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48304 p hg
    simpa only [d8151, d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48306 (p : Pattern) (guard : d8152 p = 1) : d481 p ≤ (0 : Int) + d447 p := by
  cases selected : p 48 with
  | false =>
    have hg : d8146 p = 1 := by simpa only [d8152, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41443 p hg
    simpa only [d8152, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8151 p = 1 := by simpa only [d8152, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48305 p hg
    simpa only [d8152, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48307 (p : Pattern) (guard : d8146 p = 1) : d482 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8140 p = 1 := by simpa only [d8146, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41407 p hg
    simpa only [d8146, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8145 p = 1 := by simpa only [d8146, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48289 p hg
    simpa only [d8146, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48308 (p : Pattern) (guard : d8142 p = 1) : d99 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d99, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35691 p hg
    simpa only [d8142, d99, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d99, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d99, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48309 (p : Pattern) (guard : d8143 p = 1) : d100 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d100, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35559 p hg
    simpa only [d8143, d100, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d100, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48308 p hg
    simpa only [d8143, d100, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48310 (p : Pattern) (guard : d8144 p = 1) : d101 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d101, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41447 p hg
    simpa only [d8144, d101, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d101, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48309 p hg
    simpa only [d8144, d101, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48311 (p : Pattern) (guard : d8145 p = 1) : d101 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41423 p hg
    simpa only [d8145, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48310 p hg
    simpa only [d8145, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48312 (p : Pattern) (guard : d8151 p = 1) : d483 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8145 p = 1 := by simpa only [d8151, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48311 p hg
    simpa only [d8151, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8150 p = 1 := by simpa only [d8151, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48304 p hg
    simpa only [d8151, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48313 (p : Pattern) (guard : d8152 p = 1) : d484 p ≤ (0 : Int) + d447 p := by
  cases selected : p 48 with
  | false =>
    have hg : d8146 p = 1 := by simpa only [d8152, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48307 p hg
    simpa only [d8152, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8151 p = 1 := by simpa only [d8152, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48312 p hg
    simpa only [d8152, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48314 (p : Pattern) (guard : d8139 p = 1) : d446 p ≤ (0 : Int) + d446 p := by
  omega
theorem compare48315 (p : Pattern) (guard : d8140 p = 1) : d485 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8134 p = 1 := by simpa only [d8140, d485, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41399 p hg
    simpa only [d8140, d485, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8139 p = 1 := by simpa only [d8140, d485, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48314 p hg
    simpa only [d8140, d485, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48316 (p : Pattern) (guard : d8144 p = 1) : d446 p ≤ (0 : Int) + d446 p := by
  omega
theorem compare48317 (p : Pattern) (guard : d8145 p = 1) : d485 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d485, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41423 p hg
    simpa only [d8145, d485, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d485, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48316 p hg
    simpa only [d8145, d485, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48318 (p : Pattern) (guard : d8146 p = 1) : d485 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8140 p = 1 := by simpa only [d8146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48315 p hg
    simpa only [d8146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8145 p = 1 := by simpa only [d8146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48317 p hg
    simpa only [d8146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48319 (p : Pattern) (guard : d8150 p = 1) : d486 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8144 p = 1 := by simpa only [d8150, d486, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41505 p hg
    simpa only [d8150, d486, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8149 p = 1 := by simpa only [d8150, d486, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48303 p hg
    simpa only [d8150, d486, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48320 (p : Pattern) (guard : d8151 p = 1) : d487 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8145 p = 1 := by simpa only [d8151, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48317 p hg
    simpa only [d8151, d487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8150 p = 1 := by simpa only [d8151, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48319 p hg
    simpa only [d8151, d487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48321 (p : Pattern) (guard : d8152 p = 1) : d488 p ≤ (0 : Int) + d447 p := by
  cases selected : p 48 with
  | false =>
    have hg : d8146 p = 1 := by simpa only [d8152, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48318 p hg
    simpa only [d8152, d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8151 p = 1 := by simpa only [d8152, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48320 p hg
    simpa only [d8152, d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48322 (p : Pattern) (guard : d8133 p = 1) : d426 p ≤ (0 : Int) + d426 p := by
  omega
theorem compare48323 (p : Pattern) (guard : d8134 p = 1) : d489 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8128 p = 1 := by simpa only [d8134, d489, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41391 p hg
    simpa only [d8134, d489, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8133 p = 1 := by simpa only [d8134, d489, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48322 p hg
    simpa only [d8134, d489, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48324 (p : Pattern) (guard : d8138 p = 1) : d445 p ≤ (0 : Int) + d445 p := by
  omega
theorem compare48325 (p : Pattern) (guard : d8139 p = 1) : d490 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d490, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41403 p hg
    simpa only [d8139, d490, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d490, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48324 p hg
    simpa only [d8139, d490, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48326 (p : Pattern) (guard : d8140 p = 1) : d491 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8134 p = 1 := by simpa only [d8140, d491, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48323 p hg
    simpa only [d8140, d491, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8139 p = 1 := by simpa only [d8140, d491, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48325 p hg
    simpa only [d8140, d491, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48327 (p : Pattern) (guard : d8138 p = 1) : d426 p ≤ (0 : Int) + d426 p := by
  omega
theorem compare48328 (p : Pattern) (guard : d8139 p = 1) : d489 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d489, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41415 p hg
    simpa only [d8139, d489, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d489, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48327 p hg
    simpa only [d8139, d489, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48329 (p : Pattern) (guard : d8143 p = 1) : d445 p ≤ (0 : Int) + d445 p := by
  omega
theorem compare48330 (p : Pattern) (guard : d8144 p = 1) : d492 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d492, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41433 p hg
    simpa only [d8144, d492, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d492, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48329 p hg
    simpa only [d8144, d492, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48331 (p : Pattern) (guard : d8145 p = 1) : d493 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d493, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48328 p hg
    simpa only [d8145, d493, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d493, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48330 p hg
    simpa only [d8145, d493, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48332 (p : Pattern) (guard : d8146 p = 1) : d494 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8140 p = 1 := by simpa only [d8146, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48326 p hg
    simpa only [d8146, d494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8145 p = 1 := by simpa only [d8146, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48331 p hg
    simpa only [d8146, d494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48333 (p : Pattern) (guard : d8144 p = 1) : d490 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d490, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41447 p hg
    simpa only [d8144, d490, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d490, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48329 p hg
    simpa only [d8144, d490, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48334 (p : Pattern) (guard : d8145 p = 1) : d491 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d491, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48328 p hg
    simpa only [d8145, d491, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d491, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48333 p hg
    simpa only [d8145, d491, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48335 (p : Pattern) (guard : d8143 p = 1) : d426 p ≤ (0 : Int) + d426 p := by
  omega
theorem compare48336 (p : Pattern) (guard : d8144 p = 1) : d489 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d489, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41495 p hg
    simpa only [d8144, d489, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d489, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48335 p hg
    simpa only [d8144, d489, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48337 (p : Pattern) (guard : d8149 p = 1) : d495 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8143 p = 1 := by simpa only [d8149, d495, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41513 p hg
    simpa only [d8149, d495, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8148 p = 1 := by simpa only [d8149, d495, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48302 p hg
    simpa only [d8149, d495, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48338 (p : Pattern) (guard : d8150 p = 1) : d496 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8144 p = 1 := by simpa only [d8150, d496, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48336 p hg
    simpa only [d8150, d496, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8149 p = 1 := by simpa only [d8150, d496, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48337 p hg
    simpa only [d8150, d496, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48339 (p : Pattern) (guard : d8151 p = 1) : d497 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8145 p = 1 := by simpa only [d8151, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48334 p hg
    simpa only [d8151, d497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8150 p = 1 := by simpa only [d8151, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48338 p hg
    simpa only [d8151, d497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48340 (p : Pattern) (guard : d8152 p = 1) : d498 p ≤ (0 : Int) + d447 p := by
  cases selected : p 48 with
  | false =>
    have hg : d8146 p = 1 := by simpa only [d8152, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48332 p hg
    simpa only [d8152, d498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8151 p = 1 := by simpa only [d8152, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48339 p hg
    simpa only [d8152, d498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48341 (p : Pattern) (guard : d8103 p = 1) : d362 p ≤ (0 : Int) + d362 p := by
  omega
theorem compare48342 (p : Pattern) (guard : d8104 p = 1) : d790 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8098 p = 1 := by simpa only [d8104, d790, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34371 p hg
    simpa only [d8104, d790, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8103 p = 1 := by simpa only [d8104, d790, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48341 p hg
    simpa only [d8104, d790, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48343 (p : Pattern) (guard : d8103 p = 1) : d791 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d791, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47681 p hg
    simpa only [d8103, d791, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d791, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38111 p hg
    simpa only [d8103, d791, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48344 (p : Pattern) (guard : d8108 p = 1) : d375 p ≤ (0 : Int) + d375 p := by
  omega
theorem compare48345 (p : Pattern) (guard : d8109 p = 1) : d792 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d792, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48343 p hg
    simpa only [d8109, d792, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d792, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48344 p hg
    simpa only [d8109, d792, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48346 (p : Pattern) (guard : d8110 p = 1) : d793 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8104 p = 1 := by simpa only [d8110, d793, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48342 p hg
    simpa only [d8110, d793, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8109 p = 1 := by simpa only [d8110, d793, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48345 p hg
    simpa only [d8110, d793, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48347 (p : Pattern) (guard : d8108 p = 1) : d387 p ≤ (0 : Int) + d387 p := by
  omega
theorem compare48348 (p : Pattern) (guard : d8109 p = 1) : d794 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d794, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34492 p hg
    simpa only [d8109, d794, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d794, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48347 p hg
    simpa only [d8109, d794, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48349 (p : Pattern) (guard : d8101 p = 1) : d797 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34442 p hg
    simpa only [d8101, d797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34570 p hg
    simpa only [d8101, d797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48350 (p : Pattern) (guard : d8107 p = 1) : d798 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48349 p hg
    simpa only [d8107, d798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34606 p hg
    simpa only [d8107, d798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48351 (p : Pattern) (guard : d8108 p = 1) : d799 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d799, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47707 p hg
    simpa only [d8108, d799, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d799, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48350 p hg
    simpa only [d8108, d799, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48352 (p : Pattern) (guard : d8114 p = 1) : d800 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d800, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48351 p hg
    simpa only [d8114, d800, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d800, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d800, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48353 (p : Pattern) (guard : d8115 p = 1) : d801 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d801, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48348 p hg
    simpa only [d8115, d801, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d801, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48352 p hg
    simpa only [d8115, d801, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48354 (p : Pattern) (guard : d8116 p = 1) : d802 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8110 p = 1 := by simpa only [d8116, d802, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48346 p hg
    simpa only [d8116, d802, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8115 p = 1 := by simpa only [d8116, d802, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48353 p hg
    simpa only [d8116, d802, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48355 (p : Pattern) (guard : d8108 p = 1) : d394 p ≤ (0 : Int) + d394 p := by
  omega
theorem compare48356 (p : Pattern) (guard : d8109 p = 1) : d803 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d803, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34556 p hg
    simpa only [d8109, d803, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d803, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48355 p hg
    simpa only [d8109, d803, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48357 (p : Pattern) (guard : d8108 p = 1) : d804 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d804, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47716 p hg
    simpa only [d8108, d804, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d804, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34713 p hg
    simpa only [d8108, d804, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48358 (p : Pattern) (guard : d8114 p = 1) : d805 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d805, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48357 p hg
    simpa only [d8114, d805, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d805, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d805, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48359 (p : Pattern) (guard : d8115 p = 1) : d806 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d806, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48356 p hg
    simpa only [d8115, d806, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d806, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48358 p hg
    simpa only [d8115, d806, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48360 (p : Pattern) (guard : d8114 p = 1) : d807 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d807, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34601 p hg
    simpa only [d8114, d807, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d807, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d807, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48361 (p : Pattern) (guard : d8112 p = 1) : d809 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34712 p hg
    simpa only [d8112, d809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34729 p hg
    simpa only [d8112, d809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48362 (p : Pattern) (guard : d8113 p = 1) : d810 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47722 p hg
    simpa only [d8113, d810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48361 p hg
    simpa only [d8113, d810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48363 (p : Pattern) (guard : d8119 p = 1) : d811 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48362 p hg
    simpa only [d8119, d811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48364 (p : Pattern) (guard : d8120 p = 1) : d812 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d812, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48360 p hg
    simpa only [d8120, d812, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d812, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48363 p hg
    simpa only [d8120, d812, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48365 (p : Pattern) (guard : d8121 p = 1) : d813 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d813, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48359 p hg
    simpa only [d8121, d813, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d813, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48364 p hg
    simpa only [d8121, d813, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48366 (p : Pattern) (guard : d8122 p = 1) : d814 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8116 p = 1 := by simpa only [d8122, d814, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48354 p hg
    simpa only [d8122, d814, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8121 p = 1 := by simpa only [d8122, d814, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48365 p hg
    simpa only [d8122, d814, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48367 (p : Pattern) (guard : d8108 p = 1) : d403 p ≤ (0 : Int) + d403 p := by
  omega
theorem compare48368 (p : Pattern) (guard : d8109 p = 1) : d815 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d815, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38104 p hg
    simpa only [d8109, d815, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d815, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48367 p hg
    simpa only [d8109, d815, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48369 (p : Pattern) (guard : d8108 p = 1) : d804 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d804, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47733 p hg
    simpa only [d8108, d804, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d804, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34713 p hg
    simpa only [d8108, d804, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48370 (p : Pattern) (guard : d8114 p = 1) : d805 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d805, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48369 p hg
    simpa only [d8114, d805, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d805, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d805, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48371 (p : Pattern) (guard : d8115 p = 1) : d816 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d816, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48368 p hg
    simpa only [d8115, d816, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d816, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48370 p hg
    simpa only [d8115, d816, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48372 (p : Pattern) (guard : d8113 p = 1) : d375 p ≤ (0 : Int) + d375 p := by
  omega
theorem compare48373 (p : Pattern) (guard : d8114 p = 1) : d817 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d817, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41380 p hg
    simpa only [d8114, d817, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d817, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48372 p hg
    simpa only [d8114, d817, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48374 (p : Pattern) (guard : d8120 p = 1) : d818 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d818, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48373 p hg
    simpa only [d8120, d818, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d818, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48363 p hg
    simpa only [d8120, d818, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48375 (p : Pattern) (guard : d8121 p = 1) : d819 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d819, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48371 p hg
    simpa only [d8121, d819, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d819, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48374 p hg
    simpa only [d8121, d819, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48376 (p : Pattern) (guard : d8114 p = 1) : d820 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d820, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38118 p hg
    simpa only [d8114, d820, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d820, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d820, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48377 (p : Pattern) (guard : d8120 p = 1) : d821 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d821, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48376 p hg
    simpa only [d8120, d821, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d821, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38121 p hg
    simpa only [d8120, d821, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48378 (p : Pattern) (guard : d8126 p = 1) : d822 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d822, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48377 p hg
    simpa only [d8126, d822, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d822, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41388 p hg
    simpa only [d8126, d822, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48379 (p : Pattern) (guard : d8127 p = 1) : d823 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d823, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48375 p hg
    simpa only [d8127, d823, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d823, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48378 p hg
    simpa only [d8127, d823, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48380 (p : Pattern) (guard : d8128 p = 1) : d824 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8122 p = 1 := by simpa only [d8128, d824, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48366 p hg
    simpa only [d8128, d824, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8127 p = 1 := by simpa only [d8128, d824, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48379 p hg
    simpa only [d8128, d824, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48381 (p : Pattern) (guard : d8108 p = 1) : d390 p ≤ (0 : Int) + d390 p := by
  omega
theorem compare48382 (p : Pattern) (guard : d8109 p = 1) : d825 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d825, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34631 p hg
    simpa only [d8109, d825, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d825, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48381 p hg
    simpa only [d8109, d825, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48383 (p : Pattern) (guard : d8108 p = 1) : d791 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d791, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47751 p hg
    simpa only [d8108, d791, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d791, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34713 p hg
    simpa only [d8108, d791, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48384 (p : Pattern) (guard : d8114 p = 1) : d826 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d826, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48383 p hg
    simpa only [d8114, d826, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d826, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d826, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48385 (p : Pattern) (guard : d8115 p = 1) : d827 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d827, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48382 p hg
    simpa only [d8115, d827, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d827, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48384 p hg
    simpa only [d8115, d827, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48386 (p : Pattern) (guard : d8113 p = 1) : d394 p ≤ (0 : Int) + d394 p := by
  omega
theorem compare48387 (p : Pattern) (guard : d8114 p = 1) : d828 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d828, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34670 p hg
    simpa only [d8114, d828, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d828, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48386 p hg
    simpa only [d8114, d828, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48388 (p : Pattern) (guard : d8106 p = 1) : d797 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34643 p hg
    simpa only [d8106, d797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34711 p hg
    simpa only [d8106, d797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48389 (p : Pattern) (guard : d8112 p = 1) : d798 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48388 p hg
    simpa only [d8112, d798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34729 p hg
    simpa only [d8112, d798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48390 (p : Pattern) (guard : d8113 p = 1) : d799 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d799, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47761 p hg
    simpa only [d8113, d799, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d799, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48389 p hg
    simpa only [d8113, d799, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48391 (p : Pattern) (guard : d8119 p = 1) : d800 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d800, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48390 p hg
    simpa only [d8119, d800, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d800, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d800, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48392 (p : Pattern) (guard : d8120 p = 1) : d829 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d829, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48387 p hg
    simpa only [d8120, d829, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d829, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48391 p hg
    simpa only [d8120, d829, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48393 (p : Pattern) (guard : d8121 p = 1) : d830 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d830, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48385 p hg
    simpa only [d8121, d830, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d830, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48392 p hg
    simpa only [d8121, d830, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48394 (p : Pattern) (guard : d8114 p = 1) : d831 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d831, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34703 p hg
    simpa only [d8114, d831, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d831, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d831, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48395 (p : Pattern) (guard : d8113 p = 1) : d804 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47770 p hg
    simpa only [d8113, d804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34919 p hg
    simpa only [d8113, d804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48396 (p : Pattern) (guard : d8119 p = 1) : d805 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48395 p hg
    simpa only [d8119, d805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48397 (p : Pattern) (guard : d8120 p = 1) : d832 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d832, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48394 p hg
    simpa only [d8120, d832, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d832, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48396 p hg
    simpa only [d8120, d832, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48398 (p : Pattern) (guard : d8119 p = 1) : d807 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d807, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34726 p hg
    simpa only [d8119, d807, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d807, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d807, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48399 (p : Pattern) (guard : d8117 p = 1) : d809 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34918 p hg
    simpa only [d8117, d809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3664 p hg
    simpa only [d8117, d809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48400 (p : Pattern) (guard : d8118 p = 1) : d810 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47776 p hg
    simpa only [d8118, d810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48399 p hg
    simpa only [d8118, d810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48401 (p : Pattern) (guard : d8124 p = 1) : d811 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48400 p hg
    simpa only [d8124, d811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48402 (p : Pattern) (guard : d8125 p = 1) : d812 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d812, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48398 p hg
    simpa only [d8125, d812, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d812, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48401 p hg
    simpa only [d8125, d812, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48403 (p : Pattern) (guard : d8126 p = 1) : d833 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d833, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48397 p hg
    simpa only [d8126, d833, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d833, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48402 p hg
    simpa only [d8126, d833, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48404 (p : Pattern) (guard : d8127 p = 1) : d834 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d834, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48393 p hg
    simpa only [d8127, d834, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d834, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48403 p hg
    simpa only [d8127, d834, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48405 (p : Pattern) (guard : d8114 p = 1) : d831 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d831, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38133 p hg
    simpa only [d8114, d831, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d831, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d831, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48406 (p : Pattern) (guard : d8120 p = 1) : d832 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d832, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48405 p hg
    simpa only [d8120, d832, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d832, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48396 p hg
    simpa only [d8120, d832, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48407 (p : Pattern) (guard : d8119 p = 1) : d807 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d807, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41393 p hg
    simpa only [d8119, d807, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d807, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d807, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48408 (p : Pattern) (guard : d8125 p = 1) : d812 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d812, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48407 p hg
    simpa only [d8125, d812, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d812, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48401 p hg
    simpa only [d8125, d812, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48409 (p : Pattern) (guard : d8126 p = 1) : d833 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d833, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48406 p hg
    simpa only [d8126, d833, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d833, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48408 p hg
    simpa only [d8126, d833, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48410 (p : Pattern) (guard : d8132 p = 1) : d835 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d835, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48409 p hg
    simpa only [d8132, d835, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d835, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36499 p hg
    simpa only [d8132, d835, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48411 (p : Pattern) (guard : d8133 p = 1) : d836 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d836, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48404 p hg
    simpa only [d8133, d836, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d836, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48410 p hg
    simpa only [d8133, d836, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48412 (p : Pattern) (guard : d8134 p = 1) : d837 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8128 p = 1 := by simpa only [d8134, d837, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48380 p hg
    simpa only [d8134, d837, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8133 p = 1 := by simpa only [d8134, d837, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48411 p hg
    simpa only [d8134, d837, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48413 (p : Pattern) (guard : d8108 p = 1) : d372 p ≤ (0 : Int) + d372 p := by
  omega
theorem compare48414 (p : Pattern) (guard : d8109 p = 1) : d838 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d838, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34760 p hg
    simpa only [d8109, d838, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d838, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48413 p hg
    simpa only [d8109, d838, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48415 (p : Pattern) (guard : d8108 p = 1) : d791 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d791, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47796 p hg
    simpa only [d8108, d791, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d791, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35011 p hg
    simpa only [d8108, d791, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48416 (p : Pattern) (guard : d8114 p = 1) : d826 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d826, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48415 p hg
    simpa only [d8114, d826, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d826, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d826, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48417 (p : Pattern) (guard : d8115 p = 1) : d839 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d839, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48414 p hg
    simpa only [d8115, d839, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d839, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48416 p hg
    simpa only [d8115, d839, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48418 (p : Pattern) (guard : d8113 p = 1) : d390 p ≤ (0 : Int) + d390 p := by
  omega
theorem compare48419 (p : Pattern) (guard : d8114 p = 1) : d840 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d840, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34800 p hg
    simpa only [d8114, d840, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d840, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48418 p hg
    simpa only [d8114, d840, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48420 (p : Pattern) (guard : d8113 p = 1) : d799 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d799, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47811 p hg
    simpa only [d8113, d799, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d799, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48389 p hg
    simpa only [d8113, d799, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48421 (p : Pattern) (guard : d8119 p = 1) : d800 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d800, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48420 p hg
    simpa only [d8119, d800, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d800, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d800, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48422 (p : Pattern) (guard : d8120 p = 1) : d841 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d841, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48419 p hg
    simpa only [d8120, d841, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d841, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48421 p hg
    simpa only [d8120, d841, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48423 (p : Pattern) (guard : d8121 p = 1) : d842 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d842, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48417 p hg
    simpa only [d8121, d842, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d842, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48422 p hg
    simpa only [d8121, d842, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48424 (p : Pattern) (guard : d8114 p = 1) : d843 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d843, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34822 p hg
    simpa only [d8114, d843, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d843, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48372 p hg
    simpa only [d8114, d843, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48425 (p : Pattern) (guard : d8120 p = 1) : d844 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d844, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48424 p hg
    simpa only [d8120, d844, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d844, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48396 p hg
    simpa only [d8120, d844, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48426 (p : Pattern) (guard : d8119 p = 1) : d807 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d807, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34837 p hg
    simpa only [d8119, d807, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d807, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d807, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48427 (p : Pattern) (guard : d8125 p = 1) : d812 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d812, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48426 p hg
    simpa only [d8125, d812, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d812, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48401 p hg
    simpa only [d8125, d812, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48428 (p : Pattern) (guard : d8126 p = 1) : d845 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d845, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48425 p hg
    simpa only [d8126, d845, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d845, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48427 p hg
    simpa only [d8126, d845, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48429 (p : Pattern) (guard : d8127 p = 1) : d846 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d846, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48423 p hg
    simpa only [d8127, d846, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d846, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48428 p hg
    simpa only [d8127, d846, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48430 (p : Pattern) (guard : d8114 p = 1) : d803 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d803, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35007 p hg
    simpa only [d8114, d803, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d803, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48386 p hg
    simpa only [d8114, d803, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48431 (p : Pattern) (guard : d8113 p = 1) : d804 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d804, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47827 p hg
    simpa only [d8113, d804, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d804, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34919 p hg
    simpa only [d8113, d804, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48432 (p : Pattern) (guard : d8119 p = 1) : d805 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d805, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48431 p hg
    simpa only [d8119, d805, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d805, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d805, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48433 (p : Pattern) (guard : d8120 p = 1) : d806 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d806, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48430 p hg
    simpa only [d8120, d806, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d806, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48432 p hg
    simpa only [d8120, d806, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48434 (p : Pattern) (guard : d8119 p = 1) : d807 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d807, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35022 p hg
    simpa only [d8119, d807, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d807, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d807, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48435 (p : Pattern) (guard : d8125 p = 1) : d812 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d812, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48434 p hg
    simpa only [d8125, d812, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d812, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48401 p hg
    simpa only [d8125, d812, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48436 (p : Pattern) (guard : d8126 p = 1) : d813 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d813, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48433 p hg
    simpa only [d8126, d813, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d813, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48435 p hg
    simpa only [d8126, d813, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48437 (p : Pattern) (guard : d8119 p = 1) : d820 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d820, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38149 p hg
    simpa only [d8119, d820, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d820, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d820, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48438 (p : Pattern) (guard : d8125 p = 1) : d821 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d821, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48437 p hg
    simpa only [d8125, d821, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d821, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38152 p hg
    simpa only [d8125, d821, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48439 (p : Pattern) (guard : d8131 p = 1) : d822 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d822, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48438 p hg
    simpa only [d8131, d822, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d822, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41400 p hg
    simpa only [d8131, d822, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
