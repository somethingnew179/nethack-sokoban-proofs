/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons219
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare30800 (p : Pattern) (guard : d5847 p = 1) : d3986 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30586 p hg
    simpa only [d3986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30799 p hg
    simpa only [d3986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30801 (p : Pattern) (guard : d5847 p = 1) : d3987 p ≤ (0 : Int) + d3366 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30545 p hg
    simpa only [d3987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30800 p hg
    simpa only [d3987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30802 (p : Pattern) (guard : d5847 p = 1) : d3988 p ≤ (0 : Int) + d3367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3988, d3367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30548 p hg
    simpa only [d3988, d3367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3988, d3367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3988, d3367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30803 (p : Pattern) (guard : d5847 p = 1) : d3989 p ≤ (0 : Int) + d3368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3989, d3368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30801 p hg
    simpa only [d3989, d3368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3989, d3368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30802 p hg
    simpa only [d3989, d3368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30804 (p : Pattern) (guard : d5847 p = 1) : d3990 p ≤ (0 : Int) + d3481 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3990, d3481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30803 p hg
    simpa only [d3990, d3481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3990, d3481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3990, d3481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30805 (p : Pattern) (guard : d5847 p = 1) : d3991 p ≤ (0 : Int) + d3491 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3991, d3491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30798 p hg
    simpa only [d3991, d3491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3991, d3491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30804 p hg
    simpa only [d3991, d3491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30806 (p : Pattern) (guard : d5847 p = 1) : d3992 p ≤ (0 : Int) + d3367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3992, d3367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30800 p hg
    simpa only [d3992, d3367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3992, d3367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3992, d3367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30807 (p : Pattern) (guard : d5847 p = 1) : d3993 p ≤ (0 : Int) + d3368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3993, d3368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30590 p hg
    simpa only [d3993, d3368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3993, d3368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30806 p hg
    simpa only [d3993, d3368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30808 (p : Pattern) (guard : d5847 p = 1) : d3994 p ≤ (0 : Int) + d3481 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3994, d3481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30807 p hg
    simpa only [d3994, d3481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3994, d3481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3994, d3481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30809 (p : Pattern) (guard : d5847 p = 1) : d3995 p ≤ (0 : Int) + d3483 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3995, d3483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30808 p hg
    simpa only [d3995, d3483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3995, d3483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d3995, d3483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30810 (p : Pattern) (guard : d5847 p = 1) : d3996 p ≤ (0 : Int) + d3492 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3996, d3492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30805 p hg
    simpa only [d3996, d3492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3996, d3492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30809 p hg
    simpa only [d3996, d3492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30811 (p : Pattern) (guard : d5847 p = 1) : d3997 p ≤ (0 : Int) + d3506 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3997, d3506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30590 p hg
    simpa only [d3997, d3506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3997, d3506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30581 p hg
    simpa only [d3997, d3506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30812 (p : Pattern) (guard : d5847 p = 1) : d3998 p ≤ (0 : Int) + d3507 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3998, d3507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30811 p hg
    simpa only [d3998, d3507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3998, d3507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30591 p hg
    simpa only [d3998, d3507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30813 (p : Pattern) (guard : d5847 p = 1) : d3999 p ≤ (0 : Int) + d3508 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d3999, d3508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30812 p hg
    simpa only [d3999, d3508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d3999, d3508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30789 p hg
    simpa only [d3999, d3508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30814 (p : Pattern) (guard : d5847 p = 1) : d4000 p ≤ (0 : Int) + d3509 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4000, d3509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30396 p hg
    simpa only [d4000, d3509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4000, d3509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d4000, d3509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30815 (p : Pattern) (guard : d5847 p = 1) : d4001 p ≤ (0 : Int) + d3510 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4001, d3510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30813 p hg
    simpa only [d4001, d3510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4001, d3510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30814 p hg
    simpa only [d4001, d3510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30816 (p : Pattern) (guard : d5847 p = 1) : d4002 p ≤ (0 : Int) + d3511 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4002, d3511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30810 p hg
    simpa only [d4002, d3511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4002, d3511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30815 p hg
    simpa only [d4002, d3511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30817 (p : Pattern) (guard : d5847 p = 1) : d4003 p ≤ (0 : Int) + d3512 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4003, d3512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30792 p hg
    simpa only [d4003, d3512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4003, d3512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30816 p hg
    simpa only [d4003, d3512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30818 (p : Pattern) (guard : d5847 p = 1) : d4004 p ≤ (0 : Int) + d3364 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30636 p hg
    simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30639 p hg
    simpa only [d4004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30819 (p : Pattern) (guard : d5847 p = 1) : d4005 p ≤ (0 : Int) + d3513 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4005, d3513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30646 p hg
    simpa only [d4005, d3513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4005, d3513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30424 p hg
    simpa only [d4005, d3513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30820 (p : Pattern) (guard : d5847 p = 1) : d4006 p ≤ (0 : Int) + d3514 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4006, d3514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30818 p hg
    simpa only [d4006, d3514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4006, d3514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30819 p hg
    simpa only [d4006, d3514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30821 (p : Pattern) (guard : d5847 p = 1) : d4007 p ≤ (0 : Int) + d3515 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4007, d3515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30820 p hg
    simpa only [d4007, d3515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4007, d3515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30657 p hg
    simpa only [d4007, d3515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30822 (p : Pattern) (guard : d5847 p = 1) : d4008 p ≤ (0 : Int) + d3516 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4008, d3516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30821 p hg
    simpa only [d4008, d3516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4008, d3516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30661 p hg
    simpa only [d4008, d3516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30823 (p : Pattern) (guard : d5847 p = 1) : d326 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d326, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26448 p hg
    simpa only [d5847, d326, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d326, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17682 p hg
    simpa only [d5847, d326, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30824 (p : Pattern) (guard : d5847 p = 1) : d4009 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30569 p hg
    simpa only [d4009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30823 p hg
    simpa only [d4009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30825 (p : Pattern) (guard : d5847 p = 1) : d4010 p ≤ (0 : Int) + d3374 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30568 p hg
    simpa only [d4010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30824 p hg
    simpa only [d4010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30826 (p : Pattern) (guard : d5847 p = 1) : d4011 p ≤ (0 : Int) + d3375 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4011, d3375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30825 p hg
    simpa only [d4011, d3375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4011, d3375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d4011, d3375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30827 (p : Pattern) (guard : d5847 p = 1) : d4012 p ≤ (0 : Int) + d3394 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4012, d3394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30617 p hg
    simpa only [d4012, d3394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4012, d3394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30826 p hg
    simpa only [d4012, d3394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30828 (p : Pattern) (guard : d5847 p = 1) : d4013 p ≤ (0 : Int) + d3394 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30827 p hg
    simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30646 p hg
    simpa only [d4013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30829 (p : Pattern) (guard : d5847 p = 1) : d4014 p ≤ (0 : Int) + d3517 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4014, d3517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30828 p hg
    simpa only [d4014, d3517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4014, d3517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d4014, d3517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30830 (p : Pattern) (guard : d5847 p = 1) : d4015 p ≤ (0 : Int) + d3518 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4015, d3518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30829 p hg
    simpa only [d4015, d3518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4015, d3518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30660 p hg
    simpa only [d4015, d3518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30831 (p : Pattern) (guard : d5847 p = 1) : d4016 p ≤ (0 : Int) + d3519 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4016, d3519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30460 p hg
    simpa only [d4016, d3519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4016, d3519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d4016, d3519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30832 (p : Pattern) (guard : d5847 p = 1) : d4017 p ≤ (0 : Int) + d3520 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4017, d3520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d4017, d3520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4017, d3520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d4017, d3520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30833 (p : Pattern) (guard : d5847 p = 1) : d4018 p ≤ (0 : Int) + d3521 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4018, d3521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30830 p hg
    simpa only [d4018, d3521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4018, d3521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30832 p hg
    simpa only [d4018, d3521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30834 (p : Pattern) (guard : d5847 p = 1) : d4019 p ≤ (0 : Int) + d3522 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4019, d3522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30822 p hg
    simpa only [d4019, d3522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4019, d3522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30833 p hg
    simpa only [d4019, d3522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30835 (p : Pattern) (guard : d5847 p = 1) : d4020 p ≤ (0 : Int) + d3523 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4020, d3523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30817 p hg
    simpa only [d4020, d3523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4020, d3523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30834 p hg
    simpa only [d4020, d3523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30836 (p : Pattern) (guard : d5847 p = 1) : d4021 p ≤ (0 : Int) + d3524 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4021, d3524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30646 p hg
    simpa only [d4021, d3524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4021, d3524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30459 p hg
    simpa only [d4021, d3524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30837 (p : Pattern) (guard : d5847 p = 1) : d4022 p ≤ (0 : Int) + d3525 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4022, d3525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30818 p hg
    simpa only [d4022, d3525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4022, d3525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d4022, d3525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30838 (p : Pattern) (guard : d5847 p = 1) : d4023 p ≤ (0 : Int) + d3526 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4023, d3526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30641 p hg
    simpa only [d4023, d3526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4023, d3526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30459 p hg
    simpa only [d4023, d3526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30839 (p : Pattern) (guard : d5847 p = 1) : d4024 p ≤ (0 : Int) + d3527 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4024, d3527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30838 p hg
    simpa only [d4024, d3527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4024, d3527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d4024, d3527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30840 (p : Pattern) (guard : d5847 p = 1) : d4025 p ≤ (0 : Int) + d3528 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4025, d3528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30837 p hg
    simpa only [d4025, d3528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4025, d3528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30839 p hg
    simpa only [d4025, d3528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30841 (p : Pattern) (guard : d5847 p = 1) : d4026 p ≤ (0 : Int) + d3529 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4026, d3529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30648 p hg
    simpa only [d4026, d3529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4026, d3529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30424 p hg
    simpa only [d4026, d3529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30842 (p : Pattern) (guard : d5847 p = 1) : d4027 p ≤ (0 : Int) + d3530 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4027, d3530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30841 p hg
    simpa only [d4027, d3530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4027, d3530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d4027, d3530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30843 (p : Pattern) (guard : d5847 p = 1) : d4028 p ≤ (0 : Int) + d3531 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4028, d3531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30842 p hg
    simpa only [d4028, d3531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4028, d3531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d4028, d3531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30844 (p : Pattern) (guard : d5847 p = 1) : d4029 p ≤ (0 : Int) + d3532 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4029, d3532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30840 p hg
    simpa only [d4029, d3532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4029, d3532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30843 p hg
    simpa only [d4029, d3532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30845 (p : Pattern) (guard : d5847 p = 1) : d4030 p ≤ (0 : Int) + d3533 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4030, d3533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30844 p hg
    simpa only [d4030, d3533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4030, d3533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30833 p hg
    simpa only [d4030, d3533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30846 (p : Pattern) (guard : d5847 p = 1) : d4031 p ≤ (0 : Int) + d3534 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4031, d3534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30845 p hg
    simpa only [d4031, d3534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4031, d3534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27329 p hg
    simpa only [d4031, d3534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30847 (p : Pattern) (guard : d5847 p = 1) : d4032 p ≤ (0 : Int) + d3535 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4032, d3535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30835 p hg
    simpa only [d4032, d3535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4032, d3535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30846 p hg
    simpa only [d4032, d3535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30848 (p : Pattern) (guard : d5847 p = 1) : d4033 p ≤ (0 : Int) + d3536 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4033, d3536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30776 p hg
    simpa only [d4033, d3536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4033, d3536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30847 p hg
    simpa only [d4033, d3536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30849 (p : Pattern) (guard : d5847 p = 1) : d4034 p ≤ (0 : Int) + d3537 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4034, d3537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30504 p hg
    simpa only [d4034, d3537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4034, d3537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30848 p hg
    simpa only [d4034, d3537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30850 (p : Pattern) (guard : d5847 p = 1) : d4035 p ≤ (0 : Int) + d3538 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4035, d3538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30757 p hg
    simpa only [d4035, d3538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4035, d3538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30849 p hg
    simpa only [d4035, d3538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30851 (p : Pattern) (guard : d5847 p = 1) : d4036 p ≤ (0 : Int) + d3539 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d4036, d3539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30684 p hg
    simpa only [d4036, d3539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d4036, d3539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30850 p hg
    simpa only [d4036, d3539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30852 (p : Pattern) (guard : d0 p = 1) : d313 p ≤ (9 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30853 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (9 : Int) + d0 p := by
  omega
theorem compare30854 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (9 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30855 (p : Pattern) (guard : d5843 p = 1) : d13 p ≤ (9 : Int) + d0 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30853 p hg
    simpa only [d5843, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30854 p hg
    simpa only [d5843, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30856 (p : Pattern) (guard : d6326 p = 1) : d3540 p ≤ (9 : Int) + d0 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30852 p hg
    simpa only [d6326, d3540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30855 p hg
    simpa only [d6326, d3540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30857 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (9 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30858 (p : Pattern) (guard : d6326 p = 1) : d13 p ≤ (9 : Int) + d0 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30857 p hg
    simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30855 p hg
    simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30859 (p : Pattern) (guard : d6326 p = 1) : d3541 p ≤ (9 : Int) + d0 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30856 p hg
    simpa only [d3541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30858 p hg
    simpa only [d3541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30860 (p : Pattern) (guard : d6326 p = 1) : d3542 p ≤ (9 : Int) + d0 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30859 p hg
    simpa only [d3542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30858 p hg
    simpa only [d3542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30861 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (9 : Int) + d0 p := by
  change (4 : Int) ≤ (9 : Int) + 0
  decide
theorem compare30862 (p : Pattern) (guard : d5843 p = 1) : d17 p ≤ (9 : Int) + d0 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30861 p hg
    simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30854 p hg
    simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30863 (p : Pattern) (guard : d6326 p = 1) : d3543 p ≤ (9 : Int) + d0 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30857 p hg
    simpa only [d6326, d3543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30862 p hg
    simpa only [d6326, d3543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30864 (p : Pattern) (guard : d6326 p = 1) : d3544 p ≤ (9 : Int) + d0 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30858 p hg
    simpa only [d3544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30863 p hg
    simpa only [d3544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30865 (p : Pattern) (guard : d6326 p = 1) : d3545 p ≤ (9 : Int) + d0 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30864 p hg
    simpa only [d3545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30863 p hg
    simpa only [d3545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30866 (p : Pattern) (guard : d6326 p = 1) : d3546 p ≤ (9 : Int) + d0 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30860 p hg
    simpa only [d3546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30865 p hg
    simpa only [d3546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30867 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (9 : Int) + d0 p := by
  change (2 : Int) ≤ (9 : Int) + 0
  decide
theorem compare30868 (p : Pattern) (guard : d5843 p = 1) : d30 p ≤ (9 : Int) + d0 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30867 p hg
    simpa only [d5843, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30854 p hg
    simpa only [d5843, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30869 (p : Pattern) (guard : d6326 p = 1) : d3547 p ≤ (9 : Int) + d0 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30857 p hg
    simpa only [d6326, d3547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30868 p hg
    simpa only [d6326, d3547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30870 (p : Pattern) (guard : d6326 p = 1) : d3548 p ≤ (9 : Int) + d0 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30858 p hg
    simpa only [d3548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30869 p hg
    simpa only [d3548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30871 (p : Pattern) (guard : d6326 p = 1) : d3549 p ≤ (9 : Int) + d0 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30870 p hg
    simpa only [d3549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30869 p hg
    simpa only [d3549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30872 (p : Pattern) (guard : d6326 p = 1) : d12 p ≤ (9 : Int) + d12 p := by
  omega
theorem compare30873 (p : Pattern) (guard : d6326 p = 1) : d3550 p ≤ (9 : Int) + d6327 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3550, d6327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30871 p hg
    simpa only [d3550, d6327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3550, d6327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3550, d6327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30874 (p : Pattern) (guard : d6326 p = 1) : d3551 p ≤ (9 : Int) + d6328 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3551, d6328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30866 p hg
    simpa only [d3551, d6328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3551, d6328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30873 p hg
    simpa only [d3551, d6328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30875 (p : Pattern) (guard : d6326 p = 1) : d3552 p ≤ (9 : Int) + d0 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30858 p hg
    simpa only [d3552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30865 p hg
    simpa only [d3552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30876 (p : Pattern) (guard : d6326 p = 1) : d3553 p ≤ (9 : Int) + d6328 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3553, d6328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30875 p hg
    simpa only [d3553, d6328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3553, d6328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30873 p hg
    simpa only [d3553, d6328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30877 (p : Pattern) (guard : d6326 p = 1) : d3554 p ≤ (9 : Int) + d6328 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30874 p hg
    simpa only [d3554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30876 p hg
    simpa only [d3554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30878 (p : Pattern) (guard : d0 p = 1) : d17 p ≤ (9 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30879 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (9 : Int) + d4 p := by
  omega
theorem compare30880 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (9 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30881 (p : Pattern) (guard : d5843 p = 1) : d17 p ≤ (9 : Int) + d4 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30879 p hg
    simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30880 p hg
    simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30882 (p : Pattern) (guard : d6326 p = 1) : d17 p ≤ (9 : Int) + d4 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30878 p hg
    simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30881 p hg
    simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30883 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (9 : Int) + d4 p := by
  change (8 : Int) ≤ (9 : Int) + 4
  decide
theorem compare30884 (p : Pattern) (guard : d5843 p = 1) : d190 p ≤ (9 : Int) + d4 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30883 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30880 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30885 (p : Pattern) (guard : d6326 p = 1) : d3555 p ≤ (9 : Int) + d4 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30878 p hg
    simpa only [d6326, d3555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30884 p hg
    simpa only [d6326, d3555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30886 (p : Pattern) (guard : d6326 p = 1) : d3556 p ≤ (9 : Int) + d4 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30882 p hg
    simpa only [d3556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30885 p hg
    simpa only [d3556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30887 (p : Pattern) (guard : d6326 p = 1) : d3557 p ≤ (9 : Int) + d4 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30886 p hg
    simpa only [d3557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30885 p hg
    simpa only [d3557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30888 (p : Pattern) (guard : d6326 p = 1) : d3558 p ≤ (9 : Int) + d4 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30882 p hg
    simpa only [d3558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d3558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30889 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (9 : Int) + d4 p := by
  change (6 : Int) ≤ (9 : Int) + 4
  decide
theorem compare30890 (p : Pattern) (guard : d5843 p = 1) : d34 p ≤ (9 : Int) + d4 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30889 p hg
    simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30880 p hg
    simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30891 (p : Pattern) (guard : d6326 p = 1) : d3559 p ≤ (9 : Int) + d4 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30878 p hg
    simpa only [d6326, d3559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30890 p hg
    simpa only [d6326, d3559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30892 (p : Pattern) (guard : d6326 p = 1) : d3560 p ≤ (9 : Int) + d4 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30882 p hg
    simpa only [d3560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d3560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30893 (p : Pattern) (guard : d6326 p = 1) : d3561 p ≤ (9 : Int) + d4 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30892 p hg
    simpa only [d3561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d3561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30894 (p : Pattern) (guard : d6326 p = 1) : d3562 p ≤ (9 : Int) + d6329 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3562, d6329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30893 p hg
    simpa only [d3562, d6329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3562, d6329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3562, d6329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30895 (p : Pattern) (guard : d6326 p = 1) : d3563 p ≤ (9 : Int) + d6330 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3563, d6330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30888 p hg
    simpa only [d3563, d6330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3563, d6330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30894 p hg
    simpa only [d3563, d6330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30896 (p : Pattern) (guard : d6326 p = 1) : d3564 p ≤ (9 : Int) + d6331 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3564, d6331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30876 p hg
    simpa only [d3564, d6331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3564, d6331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30895 p hg
    simpa only [d3564, d6331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30897 (p : Pattern) (guard : d6326 p = 1) : d3565 p ≤ (9 : Int) + d6332 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3565, d6332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30877 p hg
    simpa only [d3565, d6332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3565, d6332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30896 p hg
    simpa only [d3565, d6332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30898 (p : Pattern) (guard : d0 p = 1) : d23 p ≤ (9 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30899 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (9 : Int) + d9 p := by
  omega
theorem compare30900 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (9 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30901 (p : Pattern) (guard : d5843 p = 1) : d23 p ≤ (9 : Int) + d9 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30899 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30900 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30902 (p : Pattern) (guard : d6326 p = 1) : d23 p ≤ (9 : Int) + d9 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30898 p hg
    simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30901 p hg
    simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30903 (p : Pattern) (guard : d5843 p = 1) : d12 p ≤ (9 : Int) + d9 p := by
  change (12 : Int) ≤ (9 : Int) + 9
  decide
theorem compare30904 (p : Pattern) (guard : d6326 p = 1) : d356 p ≤ (9 : Int) + d9 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30898 p hg
    simpa only [d6326, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30903 p hg
    simpa only [d6326, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30905 (p : Pattern) (guard : d6326 p = 1) : d3566 p ≤ (9 : Int) + d9 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30902 p hg
    simpa only [d3566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30904 p hg
    simpa only [d3566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30906 (p : Pattern) (guard : d6326 p = 1) : d3567 p ≤ (9 : Int) + d9 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30905 p hg
    simpa only [d3567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30904 p hg
    simpa only [d3567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30907 (p : Pattern) (guard : d6326 p = 1) : d3568 p ≤ (9 : Int) + d9 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30902 p hg
    simpa only [d3568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30906 p hg
    simpa only [d3568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30908 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (9 : Int) + d9 p := by
  change (11 : Int) ≤ (9 : Int) + 9
  decide
theorem compare30909 (p : Pattern) (guard : d5843 p = 1) : d39 p ≤ (9 : Int) + d9 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30908 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30900 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30910 (p : Pattern) (guard : d6326 p = 1) : d3569 p ≤ (9 : Int) + d9 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30898 p hg
    simpa only [d6326, d3569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d6326, d3569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30911 (p : Pattern) (guard : d6326 p = 1) : d3570 p ≤ (9 : Int) + d9 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30902 p hg
    simpa only [d3570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30910 p hg
    simpa only [d3570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30912 (p : Pattern) (guard : d6326 p = 1) : d3571 p ≤ (9 : Int) + d9 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30911 p hg
    simpa only [d3571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30910 p hg
    simpa only [d3571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30913 (p : Pattern) (guard : d6326 p = 1) : d3572 p ≤ (9 : Int) + d6333 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3572, d6333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30912 p hg
    simpa only [d3572, d6333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3572, d6333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3572, d6333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30914 (p : Pattern) (guard : d6326 p = 1) : d3573 p ≤ (9 : Int) + d6334 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3573, d6334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30907 p hg
    simpa only [d3573, d6334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3573, d6334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30913 p hg
    simpa only [d3573, d6334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30915 (p : Pattern) (guard : d6326 p = 1) : d3574 p ≤ (9 : Int) + d6335 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3574, d6335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30914 p hg
    simpa only [d3574, d6335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3574, d6335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30872 p hg
    simpa only [d3574, d6335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30916 (p : Pattern) (guard : d6326 p = 1) : d3575 p ≤ (9 : Int) + d6336 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3575, d6336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30896 p hg
    simpa only [d3575, d6336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3575, d6336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30915 p hg
    simpa only [d3575, d6336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30917 (p : Pattern) (guard : d6326 p = 1) : d3576 p ≤ (9 : Int) + d6337 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3576, d6337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30897 p hg
    simpa only [d3576, d6337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3576, d6337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30916 p hg
    simpa only [d3576, d6337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30918 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (9 : Int) + d0 p := by
  change (6 : Int) ≤ (9 : Int) + 0
  decide
theorem compare30919 (p : Pattern) (guard : d5843 p = 1) : d34 p ≤ (9 : Int) + d0 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30918 p hg
    simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30854 p hg
    simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30920 (p : Pattern) (guard : d6326 p = 1) : d3577 p ≤ (9 : Int) + d0 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30857 p hg
    simpa only [d6326, d3577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30919 p hg
    simpa only [d6326, d3577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30921 (p : Pattern) (guard : d6326 p = 1) : d3578 p ≤ (9 : Int) + d0 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30858 p hg
    simpa only [d3578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30920 p hg
    simpa only [d3578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30922 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (9 : Int) + d0 p := by
  change (9 : Int) ≤ (9 : Int) + 0
  decide
theorem compare30923 (p : Pattern) (guard : d5843 p = 1) : d23 p ≤ (9 : Int) + d0 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30922 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30854 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30924 (p : Pattern) (guard : d6326 p = 1) : d3579 p ≤ (9 : Int) + d0 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30857 p hg
    simpa only [d6326, d3579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30923 p hg
    simpa only [d6326, d3579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30925 (p : Pattern) (guard : d6326 p = 1) : d3580 p ≤ (9 : Int) + d0 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30863 p hg
    simpa only [d3580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30924 p hg
    simpa only [d3580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30926 (p : Pattern) (guard : d6326 p = 1) : d3581 p ≤ (9 : Int) + d0 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30921 p hg
    simpa only [d3581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30925 p hg
    simpa only [d3581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30927 (p : Pattern) (guard : d6326 p = 1) : d3582 p ≤ (9 : Int) + d0 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30858 p hg
    simpa only [d3582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30926 p hg
    simpa only [d3582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30928 (p : Pattern) (guard : d0 p = 1) : d30 p ≤ (9 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30929 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (9 : Int) + d2 p := by
  omega
theorem compare30930 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (9 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare30931 (p : Pattern) (guard : d5843 p = 1) : d30 p ≤ (9 : Int) + d2 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30929 p hg
    simpa only [d5843, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30930 p hg
    simpa only [d5843, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30932 (p : Pattern) (guard : d6326 p = 1) : d30 p ≤ (9 : Int) + d2 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30928 p hg
    simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30931 p hg
    simpa only [d6326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30933 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (9 : Int) + d2 p := by
  change (8 : Int) ≤ (9 : Int) + 2
  decide
theorem compare30934 (p : Pattern) (guard : d5843 p = 1) : d190 p ≤ (9 : Int) + d2 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30933 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30930 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30935 (p : Pattern) (guard : d6326 p = 1) : d3583 p ≤ (9 : Int) + d2 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30928 p hg
    simpa only [d6326, d3583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30934 p hg
    simpa only [d6326, d3583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30936 (p : Pattern) (guard : d6326 p = 1) : d3584 p ≤ (9 : Int) + d2 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6326 p = 1 := by simpa only [d3584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30932 p hg
    simpa only [d3584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6326 p = 1 := by simpa only [d3584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30935 p hg
    simpa only [d3584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30937 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (9 : Int) + d2 p := by
  change (6 : Int) ≤ (9 : Int) + 2
  decide
theorem compare30938 (p : Pattern) (guard : d5843 p = 1) : d34 p ≤ (9 : Int) + d2 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30937 p hg
    simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30930 p hg
    simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30939 (p : Pattern) (guard : d6326 p = 1) : d3585 p ≤ (9 : Int) + d2 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6326, d3585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30928 p hg
    simpa only [d6326, d3585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d6326, d3585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30938 p hg
    simpa only [d6326, d3585, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
