/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons221
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare31080 (p : Pattern) (guard : d6326 p = 1) : d3691 p ≤ (9 : Int) + d6383 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3691, d6383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31069 p hg
    simpa only [d3691, d6383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3691, d6383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3691, d6383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31081 (p : Pattern) (guard : d6326 p = 1) : d3692 p ≤ (9 : Int) + d6384 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3692, d6384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31080 p hg
    simpa only [d3692, d6384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3692, d6384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3692, d6384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31082 (p : Pattern) (guard : d6326 p = 1) : d3693 p ≤ (9 : Int) + d6385 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3693, d6385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31081 p hg
    simpa only [d3693, d6385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3693, d6385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3693, d6385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31083 (p : Pattern) (guard : d6326 p = 1) : d3694 p ≤ (9 : Int) + d6386 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3694, d6386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31079 p hg
    simpa only [d3694, d6386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3694, d6386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31082 p hg
    simpa only [d3694, d6386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31084 (p : Pattern) (guard : d6326 p = 1) : d3695 p ≤ (9 : Int) + d6387 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3695, d6387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31073 p hg
    simpa only [d3695, d6387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3695, d6387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31083 p hg
    simpa only [d3695, d6387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31085 (p : Pattern) (guard : d6326 p = 1) : d3696 p ≤ (9 : Int) + d6388 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3696, d6388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31042 p hg
    simpa only [d3696, d6388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3696, d6388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31084 p hg
    simpa only [d3696, d6388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31086 (p : Pattern) (guard : d6326 p = 1) : d3697 p ≤ (9 : Int) + d6389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3697, d6389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31063 p hg
    simpa only [d3697, d6389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3697, d6389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31026 p hg
    simpa only [d3697, d6389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31087 (p : Pattern) (guard : d6326 p = 1) : d3698 p ≤ (9 : Int) + d6390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3698, d6390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31086 p hg
    simpa only [d3698, d6390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3698, d6390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31027 p hg
    simpa only [d3698, d6390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31088 (p : Pattern) (guard : d6326 p = 1) : d3699 p ≤ (9 : Int) + d6391 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3699, d6391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31027 p hg
    simpa only [d3699, d6391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3699, d6391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3699, d6391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31089 (p : Pattern) (guard : d6326 p = 1) : d3700 p ≤ (9 : Int) + d6392 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3700, d6392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31087 p hg
    simpa only [d3700, d6392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3700, d6392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31088 p hg
    simpa only [d3700, d6392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31090 (p : Pattern) (guard : d6326 p = 1) : d3701 p ≤ (9 : Int) + d6393 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3701, d6393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31088 p hg
    simpa only [d3701, d6393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3701, d6393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3701, d6393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31091 (p : Pattern) (guard : d6326 p = 1) : d3702 p ≤ (9 : Int) + d6394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3702, d6394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31089 p hg
    simpa only [d3702, d6394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3702, d6394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31090 p hg
    simpa only [d3702, d6394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31092 (p : Pattern) (guard : d6326 p = 1) : d3703 p ≤ (9 : Int) + d6395 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3703, d6395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31090 p hg
    simpa only [d3703, d6395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3703, d6395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3703, d6395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31093 (p : Pattern) (guard : d6326 p = 1) : d3704 p ≤ (9 : Int) + d6396 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3704, d6396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31091 p hg
    simpa only [d3704, d6396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3704, d6396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31092 p hg
    simpa only [d3704, d6396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31094 (p : Pattern) (guard : d6326 p = 1) : d3705 p ≤ (9 : Int) + d6397 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3705, d6397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31084 p hg
    simpa only [d3705, d6397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3705, d6397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31093 p hg
    simpa only [d3705, d6397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31095 (p : Pattern) (guard : d6326 p = 1) : d3706 p ≤ (9 : Int) + d6398 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3706, d6398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31085 p hg
    simpa only [d3706, d6398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3706, d6398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31094 p hg
    simpa only [d3706, d6398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31096 (p : Pattern) (guard : d6326 p = 1) : d3707 p ≤ (9 : Int) + d6332 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3707, d6332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30876 p hg
    simpa only [d3707, d6332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3707, d6332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30896 p hg
    simpa only [d3707, d6332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31097 (p : Pattern) (guard : d6326 p = 1) : d3708 p ≤ (9 : Int) + d6337 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3708, d6337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31096 p hg
    simpa only [d3708, d6337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3708, d6337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30916 p hg
    simpa only [d3708, d6337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31098 (p : Pattern) (guard : d6326 p = 1) : d3709 p ≤ (9 : Int) + d6354 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3709, d6354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31097 p hg
    simpa only [d3709, d6354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3709, d6354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30991 p hg
    simpa only [d3709, d6354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31099 (p : Pattern) (guard : d6326 p = 1) : d3710 p ≤ (9 : Int) + d6356 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3710, d6356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30876 p hg
    simpa only [d3710, d6356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3710, d6356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31008 p hg
    simpa only [d3710, d6356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31100 (p : Pattern) (guard : d6326 p = 1) : d3711 p ≤ (9 : Int) + d6358 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3711, d6358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31099 p hg
    simpa only [d3711, d6358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3711, d6358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31010 p hg
    simpa only [d3711, d6358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31101 (p : Pattern) (guard : d6326 p = 1) : d3712 p ≤ (9 : Int) + d6365 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3712, d6365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31100 p hg
    simpa only [d3712, d6365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3712, d6365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31028 p hg
    simpa only [d3712, d6365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31102 (p : Pattern) (guard : d6326 p = 1) : d3713 p ≤ (9 : Int) + d6376 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3713, d6376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31101 p hg
    simpa only [d3713, d6376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3713, d6376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31040 p hg
    simpa only [d3713, d6376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31103 (p : Pattern) (guard : d6326 p = 1) : d3714 p ≤ (9 : Int) + d6377 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3714, d6377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31098 p hg
    simpa only [d3714, d6377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3714, d6377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31102 p hg
    simpa only [d3714, d6377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31104 (p : Pattern) (guard : d6326 p = 1) : d3715 p ≤ (9 : Int) + d6388 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3715, d6388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31103 p hg
    simpa only [d3715, d6388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3715, d6388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31084 p hg
    simpa only [d3715, d6388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31105 (p : Pattern) (guard : d6326 p = 1) : d3716 p ≤ (9 : Int) + d6399 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3716, d6399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31084 p hg
    simpa only [d3716, d6399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3716, d6399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3716, d6399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31106 (p : Pattern) (guard : d6326 p = 1) : d3717 p ≤ (9 : Int) + d6400 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3717, d6400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31104 p hg
    simpa only [d3717, d6400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3717, d6400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31105 p hg
    simpa only [d3717, d6400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31107 (p : Pattern) (guard : d6326 p = 1) : d3718 p ≤ (9 : Int) + d6401 p := by
  cases selected : p 115 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3718, d6401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31095 p hg
    simpa only [d3718, d6401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3718, d6401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31106 p hg
    simpa only [d3718, d6401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31108 (p : Pattern) (guard : d0 p = 1) : d2051 p ≤ (9 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31109 (p : Pattern) (guard : d6326 p = 1) : d3719 p ≤ (9 : Int) + d0 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31108 p hg
    simpa only [d6326, d3719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30855 p hg
    simpa only [d6326, d3719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31110 (p : Pattern) (guard : d6326 p = 1) : d3720 p ≤ (9 : Int) + d0 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31109 p hg
    simpa only [d3720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30858 p hg
    simpa only [d3720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31111 (p : Pattern) (guard : d6326 p = 1) : d3721 p ≤ (9 : Int) + d0 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31110 p hg
    simpa only [d3721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30858 p hg
    simpa only [d3721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31112 (p : Pattern) (guard : d6326 p = 1) : d3722 p ≤ (9 : Int) + d0 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31111 p hg
    simpa only [d3722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30865 p hg
    simpa only [d3722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31113 (p : Pattern) (guard : d6326 p = 1) : d3723 p ≤ (9 : Int) + d6328 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3723, d6328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31112 p hg
    simpa only [d3723, d6328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3723, d6328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30873 p hg
    simpa only [d3723, d6328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31114 (p : Pattern) (guard : d6326 p = 1) : d3724 p ≤ (9 : Int) + d6328 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31113 p hg
    simpa only [d3724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30876 p hg
    simpa only [d3724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31115 (p : Pattern) (guard : d6326 p = 1) : d3725 p ≤ (9 : Int) + d6332 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3725, d6332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31114 p hg
    simpa only [d3725, d6332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3725, d6332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30896 p hg
    simpa only [d3725, d6332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31116 (p : Pattern) (guard : d6326 p = 1) : d3726 p ≤ (9 : Int) + d6337 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3726, d6337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31115 p hg
    simpa only [d3726, d6337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3726, d6337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30916 p hg
    simpa only [d3726, d6337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31117 (p : Pattern) (guard : d6326 p = 1) : d3727 p ≤ (9 : Int) + d6354 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3727, d6354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31116 p hg
    simpa only [d3727, d6354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3727, d6354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30991 p hg
    simpa only [d3727, d6354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31118 (p : Pattern) (guard : d6326 p = 1) : d3728 p ≤ (9 : Int) + d6377 p := by
  cases selected : p 141 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3728, d6377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31117 p hg
    simpa only [d3728, d6377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3728, d6377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31102 p hg
    simpa only [d3728, d6377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31119 (p : Pattern) (guard : d6326 p = 1) : d3729 p ≤ (9 : Int) + d6388 p := by
  cases selected : p 138 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3729, d6388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31118 p hg
    simpa only [d3729, d6388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3729, d6388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31084 p hg
    simpa only [d3729, d6388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31120 (p : Pattern) (guard : d6326 p = 1) : d3730 p ≤ (9 : Int) + d6398 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3730, d6398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31119 p hg
    simpa only [d3730, d6398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3730, d6398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31094 p hg
    simpa only [d3730, d6398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31121 (p : Pattern) (guard : d6326 p = 1) : d3731 p ≤ (9 : Int) + d6401 p := by
  cases selected : p 115 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3731, d6401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31120 p hg
    simpa only [d3731, d6401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3731, d6401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31106 p hg
    simpa only [d3731, d6401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31122 (p : Pattern) (guard : d6326 p = 1) : d3732 p ≤ (9 : Int) + d6401 p := by
  cases selected : p 71 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31107 p hg
    simpa only [d3732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31121 p hg
    simpa only [d3732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31123 (p : Pattern) (guard : d0 p = 1) : d428 p ≤ (9 : Int) + d1 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31124 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (9 : Int) + d1 p := by
  omega
theorem compare31125 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (9 : Int) + d1 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31126 (p : Pattern) (guard : d5843 p = 1) : d102 p ≤ (9 : Int) + d1 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31124 p hg
    simpa only [d5843, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31125 p hg
    simpa only [d5843, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31127 (p : Pattern) (guard : d6326 p = 1) : d3733 p ≤ (9 : Int) + d1 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31123 p hg
    simpa only [d6326, d3733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31126 p hg
    simpa only [d6326, d3733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31128 (p : Pattern) (guard : d0 p = 1) : d102 p ≤ (9 : Int) + d1 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31129 (p : Pattern) (guard : d6326 p = 1) : d102 p ≤ (9 : Int) + d1 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31128 p hg
    simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31126 p hg
    simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31130 (p : Pattern) (guard : d6326 p = 1) : d3734 p ≤ (9 : Int) + d1 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31127 p hg
    simpa only [d3734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31129 p hg
    simpa only [d3734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31131 (p : Pattern) (guard : d6326 p = 1) : d3735 p ≤ (9 : Int) + d1 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31130 p hg
    simpa only [d3735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31129 p hg
    simpa only [d3735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31132 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (9 : Int) + d1 p := by
  change (5 : Int) ≤ (9 : Int) + 1
  decide
theorem compare31133 (p : Pattern) (guard : d5843 p = 1) : d106 p ≤ (9 : Int) + d1 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31132 p hg
    simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31125 p hg
    simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31134 (p : Pattern) (guard : d6326 p = 1) : d3736 p ≤ (9 : Int) + d1 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31128 p hg
    simpa only [d6326, d3736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31133 p hg
    simpa only [d6326, d3736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31135 (p : Pattern) (guard : d6326 p = 1) : d3737 p ≤ (9 : Int) + d1 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31129 p hg
    simpa only [d3737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31134 p hg
    simpa only [d3737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31136 (p : Pattern) (guard : d6326 p = 1) : d3738 p ≤ (9 : Int) + d1 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31135 p hg
    simpa only [d3738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31134 p hg
    simpa only [d3738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31137 (p : Pattern) (guard : d6326 p = 1) : d3739 p ≤ (9 : Int) + d1 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31131 p hg
    simpa only [d3739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31136 p hg
    simpa only [d3739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31138 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (9 : Int) + d1 p := by
  change (3 : Int) ≤ (9 : Int) + 1
  decide
theorem compare31139 (p : Pattern) (guard : d5843 p = 1) : d115 p ≤ (9 : Int) + d1 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31138 p hg
    simpa only [d5843, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31125 p hg
    simpa only [d5843, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31140 (p : Pattern) (guard : d6326 p = 1) : d3740 p ≤ (9 : Int) + d1 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31128 p hg
    simpa only [d6326, d3740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31139 p hg
    simpa only [d6326, d3740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31141 (p : Pattern) (guard : d6326 p = 1) : d3741 p ≤ (9 : Int) + d1 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31129 p hg
    simpa only [d3741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31140 p hg
    simpa only [d3741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31142 (p : Pattern) (guard : d6326 p = 1) : d3742 p ≤ (9 : Int) + d1 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31141 p hg
    simpa only [d3742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31140 p hg
    simpa only [d3742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31143 (p : Pattern) (guard : d6326 p = 1) : d3743 p ≤ (9 : Int) + d6402 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3743, d6402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31142 p hg
    simpa only [d3743, d6402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3743, d6402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3743, d6402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31144 (p : Pattern) (guard : d6326 p = 1) : d3744 p ≤ (9 : Int) + d6403 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3744, d6403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31137 p hg
    simpa only [d3744, d6403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3744, d6403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31143 p hg
    simpa only [d3744, d6403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31145 (p : Pattern) (guard : d6326 p = 1) : d3745 p ≤ (9 : Int) + d1 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31129 p hg
    simpa only [d3745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31136 p hg
    simpa only [d3745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31146 (p : Pattern) (guard : d6326 p = 1) : d3746 p ≤ (9 : Int) + d6403 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3746, d6403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31145 p hg
    simpa only [d3746, d6403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3746, d6403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31143 p hg
    simpa only [d3746, d6403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31147 (p : Pattern) (guard : d6326 p = 1) : d3747 p ≤ (9 : Int) + d6403 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31144 p hg
    simpa only [d3747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31146 p hg
    simpa only [d3747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31148 (p : Pattern) (guard : d0 p = 1) : d106 p ≤ (9 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31149 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (9 : Int) + d5 p := by
  omega
theorem compare31150 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (9 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31151 (p : Pattern) (guard : d5843 p = 1) : d106 p ≤ (9 : Int) + d5 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31149 p hg
    simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31150 p hg
    simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31152 (p : Pattern) (guard : d6326 p = 1) : d106 p ≤ (9 : Int) + d5 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31148 p hg
    simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31151 p hg
    simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31153 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (9 : Int) + d5 p := by
  change (9 : Int) ≤ (9 : Int) + 5
  decide
theorem compare31154 (p : Pattern) (guard : d5843 p = 1) : d23 p ≤ (9 : Int) + d5 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31153 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31150 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31155 (p : Pattern) (guard : d6326 p = 1) : d3748 p ≤ (9 : Int) + d5 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31148 p hg
    simpa only [d6326, d3748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31154 p hg
    simpa only [d6326, d3748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31156 (p : Pattern) (guard : d6326 p = 1) : d3749 p ≤ (9 : Int) + d5 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31152 p hg
    simpa only [d3749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31155 p hg
    simpa only [d3749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31157 (p : Pattern) (guard : d6326 p = 1) : d3750 p ≤ (9 : Int) + d5 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31156 p hg
    simpa only [d3750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31155 p hg
    simpa only [d3750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31158 (p : Pattern) (guard : d6326 p = 1) : d3751 p ≤ (9 : Int) + d5 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31152 p hg
    simpa only [d3751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31157 p hg
    simpa only [d3751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31159 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (9 : Int) + d5 p := by
  change (7 : Int) ≤ (9 : Int) + 5
  decide
theorem compare31160 (p : Pattern) (guard : d5843 p = 1) : d119 p ≤ (9 : Int) + d5 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31159 p hg
    simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31150 p hg
    simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31161 (p : Pattern) (guard : d6326 p = 1) : d3752 p ≤ (9 : Int) + d5 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31148 p hg
    simpa only [d6326, d3752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31160 p hg
    simpa only [d6326, d3752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31162 (p : Pattern) (guard : d6326 p = 1) : d3753 p ≤ (9 : Int) + d5 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31152 p hg
    simpa only [d3753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31161 p hg
    simpa only [d3753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31163 (p : Pattern) (guard : d6326 p = 1) : d3754 p ≤ (9 : Int) + d5 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31162 p hg
    simpa only [d3754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31161 p hg
    simpa only [d3754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31164 (p : Pattern) (guard : d6326 p = 1) : d3755 p ≤ (9 : Int) + d6404 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3755, d6404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31163 p hg
    simpa only [d3755, d6404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3755, d6404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3755, d6404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31165 (p : Pattern) (guard : d6326 p = 1) : d3756 p ≤ (9 : Int) + d6405 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3756, d6405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31158 p hg
    simpa only [d3756, d6405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3756, d6405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31164 p hg
    simpa only [d3756, d6405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31166 (p : Pattern) (guard : d6326 p = 1) : d3757 p ≤ (9 : Int) + d6406 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3757, d6406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31146 p hg
    simpa only [d3757, d6406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3757, d6406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31165 p hg
    simpa only [d3757, d6406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31167 (p : Pattern) (guard : d6326 p = 1) : d3758 p ≤ (9 : Int) + d6407 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3758, d6407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31147 p hg
    simpa only [d3758, d6407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3758, d6407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31166 p hg
    simpa only [d3758, d6407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31168 (p : Pattern) (guard : d6326 p = 1) : d3759 p ≤ (9 : Int) + d6408 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3759, d6408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31023 p hg
    simpa only [d3759, d6408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3759, d6408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3759, d6408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31169 (p : Pattern) (guard : d6326 p = 1) : d3760 p ≤ (9 : Int) + d6409 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3760, d6409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31166 p hg
    simpa only [d3760, d6409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3760, d6409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31168 p hg
    simpa only [d3760, d6409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31170 (p : Pattern) (guard : d6326 p = 1) : d3761 p ≤ (9 : Int) + d6410 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3761, d6410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31167 p hg
    simpa only [d3761, d6410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3761, d6410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31169 p hg
    simpa only [d3761, d6410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31171 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (9 : Int) + d1 p := by
  change (7 : Int) ≤ (9 : Int) + 1
  decide
theorem compare31172 (p : Pattern) (guard : d5843 p = 1) : d119 p ≤ (9 : Int) + d1 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31171 p hg
    simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31125 p hg
    simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31173 (p : Pattern) (guard : d6326 p = 1) : d3762 p ≤ (9 : Int) + d1 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31128 p hg
    simpa only [d6326, d3762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31172 p hg
    simpa only [d6326, d3762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31174 (p : Pattern) (guard : d6326 p = 1) : d3763 p ≤ (9 : Int) + d1 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31129 p hg
    simpa only [d3763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31173 p hg
    simpa only [d3763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31175 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (9 : Int) + d1 p := by
  change (10 : Int) ≤ (9 : Int) + 1
  decide
theorem compare31176 (p : Pattern) (guard : d5843 p = 1) : d57 p ≤ (9 : Int) + d1 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31175 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31125 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31177 (p : Pattern) (guard : d6326 p = 1) : d1955 p ≤ (9 : Int) + d1 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d1955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31128 p hg
    simpa only [d6326, d1955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d1955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31176 p hg
    simpa only [d6326, d1955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31178 (p : Pattern) (guard : d6326 p = 1) : d3764 p ≤ (9 : Int) + d1 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31134 p hg
    simpa only [d3764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31177 p hg
    simpa only [d3764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31179 (p : Pattern) (guard : d6326 p = 1) : d3765 p ≤ (9 : Int) + d1 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31174 p hg
    simpa only [d3765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31178 p hg
    simpa only [d3765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31180 (p : Pattern) (guard : d6326 p = 1) : d3766 p ≤ (9 : Int) + d1 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31129 p hg
    simpa only [d3766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31179 p hg
    simpa only [d3766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31181 (p : Pattern) (guard : d0 p = 1) : d115 p ≤ (9 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31182 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (9 : Int) + d3 p := by
  omega
theorem compare31183 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (9 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31184 (p : Pattern) (guard : d5843 p = 1) : d115 p ≤ (9 : Int) + d3 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31182 p hg
    simpa only [d5843, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31183 p hg
    simpa only [d5843, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31185 (p : Pattern) (guard : d6326 p = 1) : d115 p ≤ (9 : Int) + d3 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31181 p hg
    simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31184 p hg
    simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31186 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (9 : Int) + d3 p := by
  change (9 : Int) ≤ (9 : Int) + 3
  decide
theorem compare31187 (p : Pattern) (guard : d5843 p = 1) : d23 p ≤ (9 : Int) + d3 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31186 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31183 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31188 (p : Pattern) (guard : d6326 p = 1) : d3767 p ≤ (9 : Int) + d3 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31181 p hg
    simpa only [d6326, d3767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31187 p hg
    simpa only [d6326, d3767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31189 (p : Pattern) (guard : d6326 p = 1) : d3768 p ≤ (9 : Int) + d3 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31185 p hg
    simpa only [d3768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31188 p hg
    simpa only [d3768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31190 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (9 : Int) + d3 p := by
  change (7 : Int) ≤ (9 : Int) + 3
  decide
theorem compare31191 (p : Pattern) (guard : d5843 p = 1) : d119 p ≤ (9 : Int) + d3 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31190 p hg
    simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31183 p hg
    simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31192 (p : Pattern) (guard : d6326 p = 1) : d3769 p ≤ (9 : Int) + d3 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31181 p hg
    simpa only [d6326, d3769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31191 p hg
    simpa only [d6326, d3769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31193 (p : Pattern) (guard : d5843 p = 1) : d12 p ≤ (9 : Int) + d3 p := by
  change (12 : Int) ≤ (9 : Int) + 3
  decide
theorem compare31194 (p : Pattern) (guard : d6326 p = 1) : d1896 p ≤ (9 : Int) + d3 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d1896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31181 p hg
    simpa only [d6326, d1896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d1896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31193 p hg
    simpa only [d6326, d1896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31195 (p : Pattern) (guard : d6326 p = 1) : d3770 p ≤ (9 : Int) + d3 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31192 p hg
    simpa only [d3770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31194 p hg
    simpa only [d3770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31196 (p : Pattern) (guard : d6326 p = 1) : d3771 p ≤ (9 : Int) + d3 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31189 p hg
    simpa only [d3771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31195 p hg
    simpa only [d3771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31197 (p : Pattern) (guard : d6326 p = 1) : d3772 p ≤ (9 : Int) + d6411 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3772, d6411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31196 p hg
    simpa only [d3772, d6411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3772, d6411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3772, d6411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31198 (p : Pattern) (guard : d6326 p = 1) : d3773 p ≤ (9 : Int) + d6412 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3773, d6412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31180 p hg
    simpa only [d3773, d6412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3773, d6412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31197 p hg
    simpa only [d3773, d6412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31199 (p : Pattern) (guard : d0 p = 1) : d119 p ≤ (9 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31200 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (9 : Int) + d7 p := by
  omega
theorem compare31201 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (9 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31202 (p : Pattern) (guard : d5843 p = 1) : d119 p ≤ (9 : Int) + d7 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31200 p hg
    simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31201 p hg
    simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31203 (p : Pattern) (guard : d6326 p = 1) : d119 p ≤ (9 : Int) + d7 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31199 p hg
    simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31202 p hg
    simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31204 (p : Pattern) (guard : d5843 p = 1) : d12 p ≤ (9 : Int) + d7 p := by
  change (12 : Int) ≤ (9 : Int) + 7
  decide
theorem compare31205 (p : Pattern) (guard : d6326 p = 1) : d317 p ≤ (9 : Int) + d7 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31199 p hg
    simpa only [d6326, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31204 p hg
    simpa only [d6326, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31206 (p : Pattern) (guard : d6326 p = 1) : d3774 p ≤ (9 : Int) + d7 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31203 p hg
    simpa only [d3774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31205 p hg
    simpa only [d3774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31207 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (9 : Int) + d7 p := by
  change (11 : Int) ≤ (9 : Int) + 7
  decide
theorem compare31208 (p : Pattern) (guard : d5843 p = 1) : d39 p ≤ (9 : Int) + d7 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31207 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31201 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31209 (p : Pattern) (guard : d6326 p = 1) : d3775 p ≤ (9 : Int) + d7 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31199 p hg
    simpa only [d6326, d3775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31208 p hg
    simpa only [d6326, d3775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31210 (p : Pattern) (guard : d6326 p = 1) : d3776 p ≤ (9 : Int) + d7 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31209 p hg
    simpa only [d3776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31205 p hg
    simpa only [d3776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31211 (p : Pattern) (guard : d6326 p = 1) : d3777 p ≤ (9 : Int) + d7 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31206 p hg
    simpa only [d3777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31210 p hg
    simpa only [d3777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31212 (p : Pattern) (guard : d6326 p = 1) : d3778 p ≤ (9 : Int) + d6413 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3778, d6413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31211 p hg
    simpa only [d3778, d6413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3778, d6413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3778, d6413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31213 (p : Pattern) (guard : d6326 p = 1) : d3779 p ≤ (9 : Int) + d6414 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3779, d6414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31180 p hg
    simpa only [d3779, d6414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3779, d6414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31212 p hg
    simpa only [d3779, d6414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31214 (p : Pattern) (guard : d6326 p = 1) : d3780 p ≤ (9 : Int) + d6415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3780, d6415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31198 p hg
    simpa only [d3780, d6415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3780, d6415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31213 p hg
    simpa only [d3780, d6415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31215 (p : Pattern) (guard : d6326 p = 1) : d3781 p ≤ (9 : Int) + d6416 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3781, d6416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31180 p hg
    simpa only [d3781, d6416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3781, d6416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3781, d6416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31216 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (9 : Int) + d5 p := by
  change (11 : Int) ≤ (9 : Int) + 5
  decide
theorem compare31217 (p : Pattern) (guard : d5843 p = 1) : d39 p ≤ (9 : Int) + d5 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31216 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31150 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31218 (p : Pattern) (guard : d6326 p = 1) : d3782 p ≤ (9 : Int) + d5 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31148 p hg
    simpa only [d6326, d3782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31217 p hg
    simpa only [d6326, d3782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31219 (p : Pattern) (guard : d6326 p = 1) : d3783 p ≤ (9 : Int) + d5 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31152 p hg
    simpa only [d3783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31218 p hg
    simpa only [d3783, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
