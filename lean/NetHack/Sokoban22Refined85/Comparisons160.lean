/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons159
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare22400 (p : Pattern) (guard : d5502 p = 1) : d2707 p ≤ (4 : Int) + d120 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22399 p hg
    simpa only [d5502, d2707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22348 p hg
    simpa only [d5502, d2707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22401 (p : Pattern) (guard : d5538 p = 1) : d2707 p ≤ (4 : Int) + d120 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22344 p hg
    simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22400 p hg
    simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22402 (p : Pattern) (guard : d5538 p = 1) : d2754 p ≤ (4 : Int) + d120 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22401 p hg
    simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22350 p hg
    simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22403 (p : Pattern) (guard : d5538 p = 1) : d2755 p ≤ (4 : Int) + d148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2755, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22402 p hg
    simpa only [d2755, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2755, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22351 p hg
    simpa only [d2755, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22404 (p : Pattern) (guard : d5538 p = 1) : d2756 p ≤ (4 : Int) + d149 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2756, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22398 p hg
    simpa only [d2756, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2756, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22403 p hg
    simpa only [d2756, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22405 (p : Pattern) (guard : d5538 p = 1) : d2757 p ≤ (4 : Int) + d150 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2757, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22404 p hg
    simpa only [d2757, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2757, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2757, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22406 (p : Pattern) (guard : d5538 p = 1) : d2758 p ≤ (4 : Int) + d151 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2758, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22405 p hg
    simpa only [d2758, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2758, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2758, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22407 (p : Pattern) (guard : d5538 p = 1) : d2759 p ≤ (4 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2759, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22397 p hg
    simpa only [d2759, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2759, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22406 p hg
    simpa only [d2759, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22408 (p : Pattern) (guard : d5538 p = 1) : d2760 p ≤ (4 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2760, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22391 p hg
    simpa only [d2760, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2760, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22398 p hg
    simpa only [d2760, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22409 (p : Pattern) (guard : d5538 p = 1) : d2761 p ≤ (4 : Int) + d134 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2761, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22393 p hg
    simpa only [d2761, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2761, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22193 p hg
    simpa only [d2761, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22410 (p : Pattern) (guard : d5538 p = 1) : d2762 p ≤ (4 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2762, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22408 p hg
    simpa only [d2762, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2762, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22409 p hg
    simpa only [d2762, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22411 (p : Pattern) (guard : d5538 p = 1) : d2763 p ≤ (4 : Int) + d136 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2763, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22393 p hg
    simpa only [d2763, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2763, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22198 p hg
    simpa only [d2763, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22412 (p : Pattern) (guard : d5538 p = 1) : d2764 p ≤ (4 : Int) + d137 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2764, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22411 p hg
    simpa only [d2764, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2764, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2764, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22413 (p : Pattern) (guard : d5538 p = 1) : d2765 p ≤ (4 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2765, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22410 p hg
    simpa only [d2765, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2765, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22412 p hg
    simpa only [d2765, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22414 (p : Pattern) (guard : d5538 p = 1) : d2766 p ≤ (4 : Int) + d153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2766, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22403 p hg
    simpa only [d2766, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2766, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2766, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22415 (p : Pattern) (guard : d5538 p = 1) : d2767 p ≤ (4 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2767, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22414 p hg
    simpa only [d2767, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2767, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2767, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22416 (p : Pattern) (guard : d5538 p = 1) : d2768 p ≤ (4 : Int) + d155 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2768, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22415 p hg
    simpa only [d2768, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2768, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2768, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22417 (p : Pattern) (guard : d5538 p = 1) : d2769 p ≤ (4 : Int) + d156 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2769, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22413 p hg
    simpa only [d2769, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2769, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22416 p hg
    simpa only [d2769, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22418 (p : Pattern) (guard : d5538 p = 1) : d2770 p ≤ (4 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2770, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22407 p hg
    simpa only [d2770, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2770, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22417 p hg
    simpa only [d2770, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22419 (p : Pattern) (guard : d5538 p = 1) : d2771 p ≤ (4 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2771, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22389 p hg
    simpa only [d2771, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2771, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22418 p hg
    simpa only [d2771, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22420 (p : Pattern) (guard : d5538 p = 1) : d2772 p ≤ (4 : Int) + d159 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2772, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22332 p hg
    simpa only [d2772, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2772, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2772, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22421 (p : Pattern) (guard : d5538 p = 1) : d2773 p ≤ (4 : Int) + d160 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2773, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22420 p hg
    simpa only [d2773, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2773, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2773, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22422 (p : Pattern) (guard : d5538 p = 1) : d2774 p ≤ (4 : Int) + d161 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2774, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22421 p hg
    simpa only [d2774, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2774, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2774, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22423 (p : Pattern) (guard : d5538 p = 1) : d2775 p ≤ (4 : Int) + d162 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2775, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22422 p hg
    simpa only [d2775, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2775, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2775, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22424 (p : Pattern) (guard : d5538 p = 1) : d2776 p ≤ (4 : Int) + d163 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2776, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22418 p hg
    simpa only [d2776, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2776, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22423 p hg
    simpa only [d2776, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22425 (p : Pattern) (guard : d5538 p = 1) : d2777 p ≤ (4 : Int) + d164 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2777, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22419 p hg
    simpa only [d2777, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2777, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22424 p hg
    simpa only [d2777, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22426 (p : Pattern) (guard : d5538 p = 1) : d2778 p ≤ (4 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2778, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22312 p hg
    simpa only [d2778, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2778, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22330 p hg
    simpa only [d2778, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22427 (p : Pattern) (guard : d5538 p = 1) : d2779 p ≤ (4 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2779, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22426 p hg
    simpa only [d2779, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2779, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22333 p hg
    simpa only [d2779, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22428 (p : Pattern) (guard : d5538 p = 1) : d2780 p ≤ (4 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2780, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22427 p hg
    simpa only [d2780, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2780, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22360 p hg
    simpa only [d2780, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22429 (p : Pattern) (guard : d5538 p = 1) : d2781 p ≤ (4 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2781, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22312 p hg
    simpa only [d2781, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2781, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22374 p hg
    simpa only [d2781, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22430 (p : Pattern) (guard : d5538 p = 1) : d2782 p ≤ (4 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2782, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22429 p hg
    simpa only [d2782, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2782, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22376 p hg
    simpa only [d2782, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22431 (p : Pattern) (guard : d5538 p = 1) : d2783 p ≤ (4 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2783, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22430 p hg
    simpa only [d2783, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2783, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22379 p hg
    simpa only [d2783, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22432 (p : Pattern) (guard : d5538 p = 1) : d2784 p ≤ (4 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2784, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22431 p hg
    simpa only [d2784, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2784, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22387 p hg
    simpa only [d2784, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22433 (p : Pattern) (guard : d5538 p = 1) : d2785 p ≤ (4 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2785, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22428 p hg
    simpa only [d2785, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2785, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22432 p hg
    simpa only [d2785, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22434 (p : Pattern) (guard : d5538 p = 1) : d2786 p ≤ (4 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2786, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22433 p hg
    simpa only [d2786, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2786, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22418 p hg
    simpa only [d2786, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22435 (p : Pattern) (guard : d5538 p = 1) : d2787 p ≤ (4 : Int) + d165 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2787, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22418 p hg
    simpa only [d2787, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2787, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2787, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22436 (p : Pattern) (guard : d5538 p = 1) : d2788 p ≤ (4 : Int) + d166 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2788, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22434 p hg
    simpa only [d2788, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2788, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22435 p hg
    simpa only [d2788, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22437 (p : Pattern) (guard : d5538 p = 1) : d2789 p ≤ (4 : Int) + d167 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2789, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22425 p hg
    simpa only [d2789, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2789, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22436 p hg
    simpa only [d2789, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22438 (p : Pattern) (guard : d5538 p = 1) : d2790 p ≤ (4 : Int) + d168 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2790, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22269 p hg
    simpa only [d2790, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2790, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22437 p hg
    simpa only [d2790, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22439 (p : Pattern) (guard : d5538 p = 1) : d2791 p ≤ (4 : Int) + d169 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2791, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22292 p hg
    simpa only [d2791, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2791, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22438 p hg
    simpa only [d2791, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22440 (p : Pattern) (guard : d5538 p = 1) : d2792 p ≤ (4 : Int) + d170 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2792, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22172 p hg
    simpa only [d2792, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2792, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22144 p hg
    simpa only [d2792, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22441 (p : Pattern) (guard : d5538 p = 1) : d2793 p ≤ (4 : Int) + d171 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2793, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22225 p hg
    simpa only [d2793, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2793, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22440 p hg
    simpa only [d2793, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22442 (p : Pattern) (guard : d5538 p = 1) : d2794 p ≤ (4 : Int) + d172 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2794, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22172 p hg
    simpa only [d2794, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2794, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22154 p hg
    simpa only [d2794, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22443 (p : Pattern) (guard : d5538 p = 1) : d2795 p ≤ (4 : Int) + d173 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2795, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22229 p hg
    simpa only [d2795, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2795, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2795, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22444 (p : Pattern) (guard : d5538 p = 1) : d2796 p ≤ (4 : Int) + d174 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2796, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22442 p hg
    simpa only [d2796, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2796, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22443 p hg
    simpa only [d2796, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22445 (p : Pattern) (guard : d5538 p = 1) : d2797 p ≤ (4 : Int) + d175 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2797, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22441 p hg
    simpa only [d2797, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2797, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22444 p hg
    simpa only [d2797, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22446 (p : Pattern) (guard : d5538 p = 1) : d2798 p ≤ (4 : Int) + d176 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2798, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22202 p hg
    simpa only [d2798, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2798, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22443 p hg
    simpa only [d2798, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22447 (p : Pattern) (guard : d5538 p = 1) : d2799 p ≤ (4 : Int) + d177 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2799, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22446 p hg
    simpa only [d2799, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2799, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22209 p hg
    simpa only [d2799, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22448 (p : Pattern) (guard : d5538 p = 1) : d2800 p ≤ (4 : Int) + d178 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2800, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22445 p hg
    simpa only [d2800, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2800, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22447 p hg
    simpa only [d2800, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22449 (p : Pattern) (guard : d5538 p = 1) : d2801 p ≤ (4 : Int) + d179 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2801, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22224 p hg
    simpa only [d2801, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2801, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22448 p hg
    simpa only [d2801, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22450 (p : Pattern) (guard : d5538 p = 1) : d2802 p ≤ (4 : Int) + d180 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2802, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22440 p hg
    simpa only [d2802, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2802, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22156 p hg
    simpa only [d2802, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22451 (p : Pattern) (guard : d5538 p = 1) : d2803 p ≤ (4 : Int) + d181 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2803, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22443 p hg
    simpa only [d2803, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2803, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22208 p hg
    simpa only [d2803, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22452 (p : Pattern) (guard : d5538 p = 1) : d2804 p ≤ (4 : Int) + d182 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2804, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22450 p hg
    simpa only [d2804, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2804, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22451 p hg
    simpa only [d2804, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22453 (p : Pattern) (guard : d5538 p = 1) : d2805 p ≤ (4 : Int) + d183 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2805, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22443 p hg
    simpa only [d2805, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2805, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2805, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22454 (p : Pattern) (guard : d5538 p = 1) : d2806 p ≤ (4 : Int) + d184 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2806, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22453 p hg
    simpa only [d2806, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2806, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2806, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22455 (p : Pattern) (guard : d5538 p = 1) : d2807 p ≤ (4 : Int) + d185 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2807, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22452 p hg
    simpa only [d2807, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2807, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22454 p hg
    simpa only [d2807, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22456 (p : Pattern) (guard : d5538 p = 1) : d2808 p ≤ (4 : Int) + d186 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2808, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22240 p hg
    simpa only [d2808, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2808, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22455 p hg
    simpa only [d2808, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22457 (p : Pattern) (guard : d5538 p = 1) : d2809 p ≤ (4 : Int) + d187 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2809, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22449 p hg
    simpa only [d2809, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2809, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22456 p hg
    simpa only [d2809, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22458 (p : Pattern) (guard : d5538 p = 1) : d2810 p ≤ (4 : Int) + d188 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2810, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22215 p hg
    simpa only [d2810, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2810, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22231 p hg
    simpa only [d2810, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22459 (p : Pattern) (guard : d5538 p = 1) : d2811 p ≤ (4 : Int) + d189 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2811, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22458 p hg
    simpa only [d2811, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2811, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22232 p hg
    simpa only [d2811, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22460 (p : Pattern) (guard : d0 p = 1) : d2812 p ≤ (4 : Int) + d191 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22461 (p : Pattern) (guard : d1 p = 1) : d191 p ≤ (4 : Int) + d191 p := by
  omega
theorem compare22462 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d191 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22463 (p : Pattern) (guard : d5502 p = 1) : d2812 p ≤ (4 : Int) + d191 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22461 p hg
    simpa only [d5502, d2812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22462 p hg
    simpa only [d5502, d2812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22464 (p : Pattern) (guard : d5538 p = 1) : d2812 p ≤ (4 : Int) + d191 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22460 p hg
    simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22463 p hg
    simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22465 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (4 : Int) + d8 p := by
  omega
theorem compare22466 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d8 p := by
  change (12 : Int) ≤ (4 : Int) + 8
  decide
theorem compare22467 (p : Pattern) (guard : d1 p = 1) : d190 p ≤ (4 : Int) + d8 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22465 p hg
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22466 p hg
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22468 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22466 p hg
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22469 (p : Pattern) (guard : d1 p = 1) : d315 p ≤ (4 : Int) + d191 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d315, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22467 p hg
    simpa only [d315, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d315, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22468 p hg
    simpa only [d315, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22470 (p : Pattern) (guard : d5502 p = 1) : d320 p ≤ (4 : Int) + d191 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22469 p hg
    simpa only [d5502, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22462 p hg
    simpa only [d5502, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22471 (p : Pattern) (guard : d5538 p = 1) : d2813 p ≤ (4 : Int) + d191 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, d2813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22460 p hg
    simpa only [d5538, d2813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, d2813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22470 p hg
    simpa only [d5538, d2813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22472 (p : Pattern) (guard : d5538 p = 1) : d2814 p ≤ (4 : Int) + d191 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22464 p hg
    simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22471 p hg
    simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22473 (p : Pattern) (guard : d5538 p = 1) : d2815 p ≤ (4 : Int) + d192 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2815, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22471 p hg
    simpa only [d2815, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2815, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2815, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22474 (p : Pattern) (guard : d5538 p = 1) : d2816 p ≤ (4 : Int) + d193 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2816, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22472 p hg
    simpa only [d2816, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2816, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22473 p hg
    simpa only [d2816, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22475 (p : Pattern) (guard : d5538 p = 1) : d2817 p ≤ (4 : Int) + d194 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2817, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22217 p hg
    simpa only [d2817, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2817, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22474 p hg
    simpa only [d2817, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22476 (p : Pattern) (guard : d5538 p = 1) : d2818 p ≤ (4 : Int) + d195 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2818, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22475 p hg
    simpa only [d2818, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2818, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2818, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22477 (p : Pattern) (guard : d5538 p = 1) : d2819 p ≤ (4 : Int) + d196 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2819, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22476 p hg
    simpa only [d2819, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2819, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2819, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22478 (p : Pattern) (guard : d5538 p = 1) : d2820 p ≤ (4 : Int) + d197 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2820, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22459 p hg
    simpa only [d2820, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2820, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22477 p hg
    simpa only [d2820, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22479 (p : Pattern) (guard : d5538 p = 1) : d2821 p ≤ (4 : Int) + d198 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2821, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22217 p hg
    simpa only [d2821, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2821, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22198 p hg
    simpa only [d2821, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22480 (p : Pattern) (guard : d5538 p = 1) : d2822 p ≤ (4 : Int) + d199 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2822, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22225 p hg
    simpa only [d2822, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2822, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22479 p hg
    simpa only [d2822, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22481 (p : Pattern) (guard : d5538 p = 1) : d2823 p ≤ (4 : Int) + d200 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2823, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22480 p hg
    simpa only [d2823, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2823, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22242 p hg
    simpa only [d2823, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22482 (p : Pattern) (guard : d5538 p = 1) : d2824 p ≤ (4 : Int) + d201 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2824, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22474 p hg
    simpa only [d2824, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2824, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2824, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22483 (p : Pattern) (guard : d5538 p = 1) : d2825 p ≤ (4 : Int) + d202 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2825, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22482 p hg
    simpa only [d2825, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2825, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2825, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22484 (p : Pattern) (guard : d5538 p = 1) : d2826 p ≤ (4 : Int) + d203 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2826, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22483 p hg
    simpa only [d2826, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2826, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2826, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22485 (p : Pattern) (guard : d5538 p = 1) : d2827 p ≤ (4 : Int) + d204 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2827, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22481 p hg
    simpa only [d2827, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2827, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22484 p hg
    simpa only [d2827, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22486 (p : Pattern) (guard : d5538 p = 1) : d2828 p ≤ (4 : Int) + d205 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2828, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22478 p hg
    simpa only [d2828, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2828, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22485 p hg
    simpa only [d2828, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22487 (p : Pattern) (guard : d5538 p = 1) : d2829 p ≤ (4 : Int) + d206 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2829, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22457 p hg
    simpa only [d2829, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2829, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22486 p hg
    simpa only [d2829, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22488 (p : Pattern) (guard : d5538 p = 1) : d2830 p ≤ (4 : Int) + d207 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2830, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22486 p hg
    simpa only [d2830, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2830, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2830, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22489 (p : Pattern) (guard : d5538 p = 1) : d2831 p ≤ (4 : Int) + d208 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2831, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22487 p hg
    simpa only [d2831, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2831, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22488 p hg
    simpa only [d2831, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22490 (p : Pattern) (guard : d5538 p = 1) : d2832 p ≤ (4 : Int) + d209 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2832, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22284 p hg
    simpa only [d2832, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2832, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22489 p hg
    simpa only [d2832, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22491 (p : Pattern) (guard : d5538 p = 1) : d2833 p ≤ (4 : Int) + d210 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2833, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22269 p hg
    simpa only [d2833, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2833, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22490 p hg
    simpa only [d2833, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22492 (p : Pattern) (guard : d5538 p = 1) : d2834 p ≤ (4 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2834, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22329 p hg
    simpa only [d2834, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2834, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2834, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22493 (p : Pattern) (guard : d5538 p = 1) : d2835 p ≤ (4 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2835, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22375 p hg
    simpa only [d2835, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2835, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22492 p hg
    simpa only [d2835, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22494 (p : Pattern) (guard : d5538 p = 1) : d2836 p ≤ (4 : Int) + d213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2836, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22492 p hg
    simpa only [d2836, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2836, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2836, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22495 (p : Pattern) (guard : d5538 p = 1) : d2837 p ≤ (4 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2837, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22493 p hg
    simpa only [d2837, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2837, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22494 p hg
    simpa only [d2837, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22496 (p : Pattern) (guard : d5538 p = 1) : d2838 p ≤ (4 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2838, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22355 p hg
    simpa only [d2838, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2838, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2838, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22497 (p : Pattern) (guard : d5538 p = 1) : d2839 p ≤ (4 : Int) + d216 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2839, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22382 p hg
    simpa only [d2839, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2839, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22496 p hg
    simpa only [d2839, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22498 (p : Pattern) (guard : d5538 p = 1) : d2840 p ≤ (4 : Int) + d217 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2840, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22496 p hg
    simpa only [d2840, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2840, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2840, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22499 (p : Pattern) (guard : d5538 p = 1) : d2841 p ≤ (4 : Int) + d218 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2841, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22497 p hg
    simpa only [d2841, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2841, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22498 p hg
    simpa only [d2841, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22500 (p : Pattern) (guard : d5538 p = 1) : d2842 p ≤ (4 : Int) + d219 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2842, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22495 p hg
    simpa only [d2842, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2842, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22499 p hg
    simpa only [d2842, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22501 (p : Pattern) (guard : d5538 p = 1) : d2843 p ≤ (4 : Int) + d220 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2843, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22361 p hg
    simpa only [d2843, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2843, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22500 p hg
    simpa only [d2843, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22502 (p : Pattern) (guard : d5538 p = 1) : d2844 p ≤ (4 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2844, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22393 p hg
    simpa only [d2844, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2844, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2844, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22503 (p : Pattern) (guard : d5538 p = 1) : d2845 p ≤ (4 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2845, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22408 p hg
    simpa only [d2845, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2845, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22502 p hg
    simpa only [d2845, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22504 (p : Pattern) (guard : d5538 p = 1) : d2846 p ≤ (4 : Int) + d213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2846, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22502 p hg
    simpa only [d2846, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2846, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2846, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22505 (p : Pattern) (guard : d5538 p = 1) : d2847 p ≤ (4 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2847, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22503 p hg
    simpa only [d2847, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2847, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22504 p hg
    simpa only [d2847, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22506 (p : Pattern) (guard : d5538 p = 1) : d2848 p ≤ (4 : Int) + d221 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2848, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22505 p hg
    simpa only [d2848, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2848, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22416 p hg
    simpa only [d2848, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22507 (p : Pattern) (guard : d5538 p = 1) : d2849 p ≤ (4 : Int) + d222 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2849, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22407 p hg
    simpa only [d2849, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2849, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22506 p hg
    simpa only [d2849, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22508 (p : Pattern) (guard : d5538 p = 1) : d2850 p ≤ (4 : Int) + d223 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2850, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22501 p hg
    simpa only [d2850, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2850, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22507 p hg
    simpa only [d2850, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22509 (p : Pattern) (guard : d5538 p = 1) : d2851 p ≤ (4 : Int) + d224 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2851, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22507 p hg
    simpa only [d2851, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2851, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22423 p hg
    simpa only [d2851, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22510 (p : Pattern) (guard : d5538 p = 1) : d2852 p ≤ (4 : Int) + d225 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2852, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22508 p hg
    simpa only [d2852, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2852, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22509 p hg
    simpa only [d2852, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22511 (p : Pattern) (guard : d5538 p = 1) : d2853 p ≤ (4 : Int) + d226 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2853, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22368 p hg
    simpa only [d2853, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2853, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22351 p hg
    simpa only [d2853, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22512 (p : Pattern) (guard : d5538 p = 1) : d2854 p ≤ (4 : Int) + d227 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2854, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22398 p hg
    simpa only [d2854, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2854, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22511 p hg
    simpa only [d2854, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22513 (p : Pattern) (guard : d5538 p = 1) : d2855 p ≤ (4 : Int) + d228 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2855, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22512 p hg
    simpa only [d2855, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2855, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22496 p hg
    simpa only [d2855, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22514 (p : Pattern) (guard : d5538 p = 1) : d2856 p ≤ (4 : Int) + d229 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2856, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22402 p hg
    simpa only [d2856, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2856, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2856, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22515 (p : Pattern) (guard : d5538 p = 1) : d2857 p ≤ (4 : Int) + d230 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2857, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22514 p hg
    simpa only [d2857, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2857, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2857, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22516 (p : Pattern) (guard : d5538 p = 1) : d2858 p ≤ (4 : Int) + d231 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2858, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22515 p hg
    simpa only [d2858, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2858, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2858, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22517 (p : Pattern) (guard : d5538 p = 1) : d2859 p ≤ (4 : Int) + d232 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2859, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22513 p hg
    simpa only [d2859, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2859, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22516 p hg
    simpa only [d2859, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22518 (p : Pattern) (guard : d5538 p = 1) : d2860 p ≤ (4 : Int) + d233 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2860, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22397 p hg
    simpa only [d2860, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2860, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22517 p hg
    simpa only [d2860, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22519 (p : Pattern) (guard : d5538 p = 1) : d2861 p ≤ (4 : Int) + d234 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2861, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22323 p hg
    simpa only [d2861, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2861, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22351 p hg
    simpa only [d2861, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22520 (p : Pattern) (guard : d5538 p = 1) : d2862 p ≤ (4 : Int) + d235 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2862, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22519 p hg
    simpa only [d2862, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2862, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22355 p hg
    simpa only [d2862, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22521 (p : Pattern) (guard : d5538 p = 1) : d2863 p ≤ (4 : Int) + d236 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2863, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22520 p hg
    simpa only [d2863, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2863, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22515 p hg
    simpa only [d2863, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22522 (p : Pattern) (guard : d5538 p = 1) : d2864 p ≤ (4 : Int) + d237 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2864, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22162 p hg
    simpa only [d2864, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2864, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2864, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22523 (p : Pattern) (guard : d5538 p = 1) : d2865 p ≤ (4 : Int) + d238 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2865, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22521 p hg
    simpa only [d2865, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2865, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22522 p hg
    simpa only [d2865, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22524 (p : Pattern) (guard : d5538 p = 1) : d2866 p ≤ (4 : Int) + d239 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2866, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22505 p hg
    simpa only [d2866, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2866, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22523 p hg
    simpa only [d2866, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22525 (p : Pattern) (guard : d5538 p = 1) : d2867 p ≤ (4 : Int) + d240 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2867, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22518 p hg
    simpa only [d2867, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2867, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22524 p hg
    simpa only [d2867, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22526 (p : Pattern) (guard : d5538 p = 1) : d2868 p ≤ (4 : Int) + d241 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2868, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22398 p hg
    simpa only [d2868, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2868, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22198 p hg
    simpa only [d2868, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22527 (p : Pattern) (guard : d5538 p = 1) : d2869 p ≤ (4 : Int) + d242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2869, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22391 p hg
    simpa only [d2869, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2869, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22526 p hg
    simpa only [d2869, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22528 (p : Pattern) (guard : d5538 p = 1) : d2870 p ≤ (4 : Int) + d243 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2870, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22527 p hg
    simpa only [d2870, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2870, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22412 p hg
    simpa only [d2870, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22529 (p : Pattern) (guard : d5538 p = 1) : d2871 p ≤ (4 : Int) + d244 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2871, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22528 p hg
    simpa only [d2871, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2871, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22416 p hg
    simpa only [d2871, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22530 (p : Pattern) (guard : d5538 p = 1) : d2872 p ≤ (4 : Int) + d245 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2872, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22398 p hg
    simpa only [d2872, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2872, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22502 p hg
    simpa only [d2872, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22531 (p : Pattern) (guard : d5538 p = 1) : d2873 p ≤ (4 : Int) + d246 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2873, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22530 p hg
    simpa only [d2873, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2873, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22415 p hg
    simpa only [d2873, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22532 (p : Pattern) (guard : d5538 p = 1) : d2874 p ≤ (4 : Int) + d247 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2874, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22222 p hg
    simpa only [d2874, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2874, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2874, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22533 (p : Pattern) (guard : d5538 p = 1) : d2875 p ≤ (4 : Int) + d248 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2875, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22532 p hg
    simpa only [d2875, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2875, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2875, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22534 (p : Pattern) (guard : d5538 p = 1) : d2876 p ≤ (4 : Int) + d249 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2876, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22531 p hg
    simpa only [d2876, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2876, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22533 p hg
    simpa only [d2876, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22535 (p : Pattern) (guard : d5538 p = 1) : d2877 p ≤ (4 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2877, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22529 p hg
    simpa only [d2877, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2877, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22534 p hg
    simpa only [d2877, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22536 (p : Pattern) (guard : d5538 p = 1) : d2878 p ≤ (4 : Int) + d251 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2878, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22525 p hg
    simpa only [d2878, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2878, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22535 p hg
    simpa only [d2878, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22537 (p : Pattern) (guard : d5538 p = 1) : d2879 p ≤ (4 : Int) + d252 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2879, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22398 p hg
    simpa only [d2879, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2879, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22221 p hg
    simpa only [d2879, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22538 (p : Pattern) (guard : d5538 p = 1) : d2880 p ≤ (4 : Int) + d253 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2880, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22391 p hg
    simpa only [d2880, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2880, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22537 p hg
    simpa only [d2880, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22539 (p : Pattern) (guard : d5538 p = 1) : d2881 p ≤ (4 : Int) + d254 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2881, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22393 p hg
    simpa only [d2881, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2881, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22221 p hg
    simpa only [d2881, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
