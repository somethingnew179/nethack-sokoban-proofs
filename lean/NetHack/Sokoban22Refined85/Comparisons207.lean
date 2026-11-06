/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons206
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare28980 (p : Pattern) (guard : d5843 p = 1) : d5 p ≤ (0 : Int) + d1880 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14654 p hg
    simpa only [d5843, d1880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28979 p hg
    simpa only [d5843, d1880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28981 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d1881 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3366, d1881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28980 p hg
    simpa only [d5847, d3366, d1881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3366, d1881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20290 p hg
    simpa only [d5847, d3366, d1881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28982 (p : Pattern) (guard : d5854 p = 1) : d3366 p ≤ (0 : Int) + d2693 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28981 p hg
    simpa only [d5854, d2693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26786 p hg
    simpa only [d5854, d2693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28983 (p : Pattern) (guard : d5855 p = 1) : d3366 p ≤ (0 : Int) + d2694 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28969 p hg
    simpa only [d5855, d2694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28982 p hg
    simpa only [d5855, d2694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28984 (p : Pattern) (guard : d5855 p = 1) : d3367 p ≤ (0 : Int) + d2695 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3367, d2695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28983 p hg
    simpa only [d3367, d2695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3367, d2695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3367, d2695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28985 (p : Pattern) (guard : d5855 p = 1) : d3368 p ≤ (0 : Int) + d2696 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3368, d2696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d3368, d2696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3368, d2696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28984 p hg
    simpa only [d3368, d2696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28986 (p : Pattern) (guard : d5855 p = 1) : d3369 p ≤ (0 : Int) + d2697 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3369, d2697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28967 p hg
    simpa only [d3369, d2697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3369, d2697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28985 p hg
    simpa only [d3369, d2697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28987 (p : Pattern) (guard : d5855 p = 1) : d3370 p ≤ (0 : Int) + d2698 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3370, d2698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28968 p hg
    simpa only [d3370, d2698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3370, d2698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28986 p hg
    simpa only [d3370, d2698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28988 (p : Pattern) (guard : d5855 p = 1) : d3371 p ≤ (0 : Int) + d2699 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3371, d2699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28844 p hg
    simpa only [d3371, d2699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3371, d2699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3371, d2699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28989 (p : Pattern) (guard : d5855 p = 1) : d3372 p ≤ (0 : Int) + d2700 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3372, d2700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28986 p hg
    simpa only [d3372, d2700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3372, d2700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28988 p hg
    simpa only [d3372, d2700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28990 (p : Pattern) (guard : d5855 p = 1) : d3373 p ≤ (0 : Int) + d2701 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3373, d2701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28987 p hg
    simpa only [d3373, d2701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3373, d2701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28989 p hg
    simpa only [d3373, d2701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28991 (p : Pattern) (guard : d5851 p = 1) : d3374 p ≤ (0 : Int) + d2702 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26795 p hg
    simpa only [d5851, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26796 p hg
    simpa only [d5851, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28992 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (0 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28993 (p : Pattern) (guard : d5843 p = 1) : d3 p ≤ (0 : Int) + d1894 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14667 p hg
    simpa only [d5843, d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28992 p hg
    simpa only [d5843, d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28994 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d1895 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3374, d1895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28993 p hg
    simpa only [d5847, d3374, d1895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3374, d1895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20290 p hg
    simpa only [d5847, d3374, d1895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28995 (p : Pattern) (guard : d5854 p = 1) : d3374 p ≤ (0 : Int) + d2703 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28994 p hg
    simpa only [d5854, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26796 p hg
    simpa only [d5854, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28996 (p : Pattern) (guard : d5855 p = 1) : d3374 p ≤ (0 : Int) + d2704 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28991 p hg
    simpa only [d5855, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28995 p hg
    simpa only [d5855, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28997 (p : Pattern) (guard : d5855 p = 1) : d3375 p ≤ (0 : Int) + d2705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3375, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28996 p hg
    simpa only [d3375, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3375, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3375, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28998 (p : Pattern) (guard : d5855 p = 1) : d3376 p ≤ (0 : Int) + d2706 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3376, d2706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28966 p hg
    simpa only [d3376, d2706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3376, d2706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28997 p hg
    simpa only [d3376, d2706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28999 (p : Pattern) (guard : d5851 p = 1) : d3377 p ≤ (0 : Int) + d2707 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26800 p hg
    simpa only [d5851, d2707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26801 p hg
    simpa only [d5851, d2707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29000 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (0 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29001 (p : Pattern) (guard : d5843 p = 1) : d7 p ≤ (0 : Int) + d1902 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14675 p hg
    simpa only [d5843, d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29000 p hg
    simpa only [d5843, d1902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29002 (p : Pattern) (guard : d5847 p = 1) : d3377 p ≤ (0 : Int) + d1903 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3377, d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29001 p hg
    simpa only [d5847, d3377, d1903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3377, d1903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20007 p hg
    simpa only [d5847, d3377, d1903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29003 (p : Pattern) (guard : d5854 p = 1) : d3377 p ≤ (0 : Int) + d2708 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29002 p hg
    simpa only [d5854, d2708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26801 p hg
    simpa only [d5854, d2708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29004 (p : Pattern) (guard : d5855 p = 1) : d3377 p ≤ (0 : Int) + d2709 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28999 p hg
    simpa only [d5855, d2709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29003 p hg
    simpa only [d5855, d2709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29005 (p : Pattern) (guard : d5855 p = 1) : d3378 p ≤ (0 : Int) + d2710 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3378, d2710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29004 p hg
    simpa only [d3378, d2710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3378, d2710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3378, d2710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29006 (p : Pattern) (guard : d5855 p = 1) : d3379 p ≤ (0 : Int) + d2711 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3379, d2711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28966 p hg
    simpa only [d3379, d2711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3379, d2711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29005 p hg
    simpa only [d3379, d2711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29007 (p : Pattern) (guard : d5855 p = 1) : d3380 p ≤ (0 : Int) + d2712 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3380, d2712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28998 p hg
    simpa only [d3380, d2712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3380, d2712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29006 p hg
    simpa only [d3380, d2712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29008 (p : Pattern) (guard : d5855 p = 1) : d3381 p ≤ (0 : Int) + d2713 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3381, d2713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28966 p hg
    simpa only [d3381, d2713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3381, d2713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3381, d2713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29009 (p : Pattern) (guard : d5855 p = 1) : d3382 p ≤ (0 : Int) + d2714 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3382, d2714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d3382, d2714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3382, d2714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3382, d2714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29010 (p : Pattern) (guard : d5855 p = 1) : d3383 p ≤ (0 : Int) + d2715 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3383, d2715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29008 p hg
    simpa only [d3383, d2715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3383, d2715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29009 p hg
    simpa only [d3383, d2715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29011 (p : Pattern) (guard : d5855 p = 1) : d3384 p ≤ (0 : Int) + d2716 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3384, d2716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29007 p hg
    simpa only [d3384, d2716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3384, d2716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29010 p hg
    simpa only [d3384, d2716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29012 (p : Pattern) (guard : d5855 p = 1) : d3385 p ≤ (0 : Int) + d2717 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3385, d2717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28858 p hg
    simpa only [d3385, d2717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3385, d2717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3385, d2717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29013 (p : Pattern) (guard : d5855 p = 1) : d3386 p ≤ (0 : Int) + d2718 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3386, d2718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29010 p hg
    simpa only [d3386, d2718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3386, d2718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29012 p hg
    simpa only [d3386, d2718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29014 (p : Pattern) (guard : d5855 p = 1) : d3387 p ≤ (0 : Int) + d2719 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3387, d2719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29011 p hg
    simpa only [d3387, d2719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3387, d2719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d3387, d2719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29015 (p : Pattern) (guard : d5855 p = 1) : d3388 p ≤ (0 : Int) + d2720 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3388, d2720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28990 p hg
    simpa only [d3388, d2720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3388, d2720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29014 p hg
    simpa only [d3388, d2720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29016 (p : Pattern) (guard : d0 p = 1) : d3358 p ≤ (0 : Int) + d327 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29017 (p : Pattern) (guard : d5851 p = 1) : d3390 p ≤ (0 : Int) + d2721 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d3390, d2721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26815 p hg
    simpa only [d5851, d3390, d2721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d3390, d2721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29016 p hg
    simpa only [d5851, d3390, d2721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29018 (p : Pattern) (guard : d5855 p = 1) : d3391 p ≤ (0 : Int) + d2722 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d3391, d2722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d5855, d3391, d2722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d3391, d2722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28949 p hg
    simpa only [d5855, d3391, d2722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29019 (p : Pattern) (guard : d5855 p = 1) : d3392 p ≤ (0 : Int) + d2723 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3392, d2723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29018 p hg
    simpa only [d3392, d2723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3392, d2723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d3392, d2723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29020 (p : Pattern) (guard : d5855 p = 1) : d3393 p ≤ (0 : Int) + d2724 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3393, d2724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29019 p hg
    simpa only [d3393, d2724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3393, d2724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28963 p hg
    simpa only [d3393, d2724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29021 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d116 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3374, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23681 p hg
    simpa only [d5847, d3374, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3374, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20238 p hg
    simpa only [d5847, d3374, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29022 (p : Pattern) (guard : d5854 p = 1) : d3374 p ≤ (0 : Int) + d2702 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29021 p hg
    simpa only [d5854, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26796 p hg
    simpa only [d5854, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29023 (p : Pattern) (guard : d5855 p = 1) : d3374 p ≤ (0 : Int) + d2702 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28991 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29022 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29024 (p : Pattern) (guard : d5855 p = 1) : d3374 p ≤ (0 : Int) + d2725 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29023 p hg
    simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28996 p hg
    simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29025 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29026 (p : Pattern) (guard : d5843 p = 1) : d3 p ≤ (0 : Int) + d1918 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14667 p hg
    simpa only [d5843, d1918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29025 p hg
    simpa only [d5843, d1918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29027 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d1919 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3374, d1919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29026 p hg
    simpa only [d5847, d3374, d1919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3374, d1919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20170 p hg
    simpa only [d5847, d3374, d1919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29028 (p : Pattern) (guard : d5854 p = 1) : d3374 p ≤ (0 : Int) + d2726 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29027 p hg
    simpa only [d5854, d2726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26796 p hg
    simpa only [d5854, d2726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29029 (p : Pattern) (guard : d5855 p = 1) : d3374 p ≤ (0 : Int) + d2727 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28991 p hg
    simpa only [d5855, d2727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29028 p hg
    simpa only [d5855, d2727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29030 (p : Pattern) (guard : d5855 p = 1) : d3375 p ≤ (0 : Int) + d2728 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3375, d2728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29029 p hg
    simpa only [d3375, d2728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3375, d2728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3375, d2728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29031 (p : Pattern) (guard : d5855 p = 1) : d3394 p ≤ (0 : Int) + d2729 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3394, d2729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29024 p hg
    simpa only [d3394, d2729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3394, d2729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29030 p hg
    simpa only [d3394, d2729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29032 (p : Pattern) (guard : d5855 p = 1) : d3395 p ≤ (0 : Int) + d2730 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3395, d2730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29020 p hg
    simpa only [d3395, d2730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3395, d2730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29031 p hg
    simpa only [d3395, d2730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29033 (p : Pattern) (guard : d5855 p = 1) : d3396 p ≤ (0 : Int) + d2731 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3396, d2731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28985 p hg
    simpa only [d3396, d2731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3396, d2731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28844 p hg
    simpa only [d3396, d2731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29034 (p : Pattern) (guard : d5855 p = 1) : d3397 p ≤ (0 : Int) + d2732 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3397, d2732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29032 p hg
    simpa only [d3397, d2732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3397, d2732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29033 p hg
    simpa only [d3397, d2732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29035 (p : Pattern) (guard : d5855 p = 1) : d3398 p ≤ (0 : Int) + d2733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3398, d2733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28985 p hg
    simpa only [d3398, d2733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3398, d2733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28850 p hg
    simpa only [d3398, d2733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29036 (p : Pattern) (guard : d5855 p = 1) : d3399 p ≤ (0 : Int) + d2734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3399, d2734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d3399, d2734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3399, d2734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3399, d2734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29037 (p : Pattern) (guard : d5855 p = 1) : d3400 p ≤ (0 : Int) + d2735 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3400, d2735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29034 p hg
    simpa only [d3400, d2735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3400, d2735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29036 p hg
    simpa only [d3400, d2735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29038 (p : Pattern) (guard : d5855 p = 1) : d3401 p ≤ (0 : Int) + d2736 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3401, d2736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29024 p hg
    simpa only [d3401, d2736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3401, d2736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3401, d2736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29039 (p : Pattern) (guard : d5855 p = 1) : d3402 p ≤ (0 : Int) + d2737 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3402, d2737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29006 p hg
    simpa only [d3402, d2737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3402, d2737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29038 p hg
    simpa only [d3402, d2737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29040 (p : Pattern) (guard : d5855 p = 1) : d3403 p ≤ (0 : Int) + d2738 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3403, d2738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29009 p hg
    simpa only [d3403, d2738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3403, d2738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28858 p hg
    simpa only [d3403, d2738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29041 (p : Pattern) (guard : d5855 p = 1) : d3404 p ≤ (0 : Int) + d2739 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3404, d2739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29039 p hg
    simpa only [d3404, d2739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3404, d2739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29040 p hg
    simpa only [d3404, d2739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29042 (p : Pattern) (guard : d5855 p = 1) : d3405 p ≤ (0 : Int) + d2740 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3405, d2740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29009 p hg
    simpa only [d3405, d2740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3405, d2740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28860 p hg
    simpa only [d3405, d2740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29043 (p : Pattern) (guard : d5855 p = 1) : d3406 p ≤ (0 : Int) + d2741 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3406, d2741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29042 p hg
    simpa only [d3406, d2741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3406, d2741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3406, d2741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29044 (p : Pattern) (guard : d5855 p = 1) : d3407 p ≤ (0 : Int) + d2742 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3407, d2742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29041 p hg
    simpa only [d3407, d2742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3407, d2742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29043 p hg
    simpa only [d3407, d2742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29045 (p : Pattern) (guard : d5855 p = 1) : d3408 p ≤ (0 : Int) + d2743 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3408, d2743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29037 p hg
    simpa only [d3408, d2743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3408, d2743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29044 p hg
    simpa only [d3408, d2743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29046 (p : Pattern) (guard : d5855 p = 1) : d3409 p ≤ (0 : Int) + d2744 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3409, d2744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29015 p hg
    simpa only [d3409, d2744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3409, d2744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29045 p hg
    simpa only [d3409, d2744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29047 (p : Pattern) (guard : d5855 p = 1) : d3362 p ≤ (0 : Int) + d2745 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3362, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d3362, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3362, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3362, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29048 (p : Pattern) (guard : d5855 p = 1) : d3364 p ≤ (0 : Int) + d2746 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3364, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28966 p hg
    simpa only [d3364, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3364, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29047 p hg
    simpa only [d3364, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29049 (p : Pattern) (guard : d5855 p = 1) : d3367 p ≤ (0 : Int) + d2747 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3367, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28977 p hg
    simpa only [d3367, d2747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3367, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3367, d2747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29050 (p : Pattern) (guard : d5855 p = 1) : d3368 p ≤ (0 : Int) + d2748 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3368, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d3368, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3368, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29049 p hg
    simpa only [d3368, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29051 (p : Pattern) (guard : d5855 p = 1) : d3369 p ≤ (0 : Int) + d2749 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3369, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29048 p hg
    simpa only [d3369, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3369, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29050 p hg
    simpa only [d3369, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29052 (p : Pattern) (guard : d5855 p = 1) : d3410 p ≤ (0 : Int) + d2750 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3410, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29048 p hg
    simpa only [d3410, d2750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3410, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29051 p hg
    simpa only [d3410, d2750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29053 (p : Pattern) (guard : d5855 p = 1) : d3372 p ≤ (0 : Int) + d2751 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3372, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29051 p hg
    simpa only [d3372, d2751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3372, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28988 p hg
    simpa only [d3372, d2751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29054 (p : Pattern) (guard : d5855 p = 1) : d3411 p ≤ (0 : Int) + d2752 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3411, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29052 p hg
    simpa only [d3411, d2752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3411, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29053 p hg
    simpa only [d3411, d2752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29055 (p : Pattern) (guard : d5855 p = 1) : d3394 p ≤ (0 : Int) + d2753 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3394, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29024 p hg
    simpa only [d3394, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3394, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28997 p hg
    simpa only [d3394, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29056 (p : Pattern) (guard : d5847 p = 1) : d3377 p ≤ (0 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3377, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23717 p hg
    simpa only [d5847, d3377, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3377, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20290 p hg
    simpa only [d5847, d3377, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29057 (p : Pattern) (guard : d5854 p = 1) : d3377 p ≤ (0 : Int) + d2707 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29056 p hg
    simpa only [d5854, d2707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26801 p hg
    simpa only [d5854, d2707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29058 (p : Pattern) (guard : d5855 p = 1) : d3377 p ≤ (0 : Int) + d2707 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28999 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29057 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29059 (p : Pattern) (guard : d5855 p = 1) : d3377 p ≤ (0 : Int) + d2754 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29058 p hg
    simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29004 p hg
    simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29060 (p : Pattern) (guard : d5855 p = 1) : d3412 p ≤ (0 : Int) + d2755 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3412, d2755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29059 p hg
    simpa only [d3412, d2755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3412, d2755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29005 p hg
    simpa only [d3412, d2755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29061 (p : Pattern) (guard : d5855 p = 1) : d3413 p ≤ (0 : Int) + d2756 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3413, d2756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29055 p hg
    simpa only [d3413, d2756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3413, d2756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29060 p hg
    simpa only [d3413, d2756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29062 (p : Pattern) (guard : d5855 p = 1) : d3414 p ≤ (0 : Int) + d2757 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3414, d2757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29061 p hg
    simpa only [d3414, d2757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3414, d2757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3414, d2757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29063 (p : Pattern) (guard : d5855 p = 1) : d3415 p ≤ (0 : Int) + d2758 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3415, d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29062 p hg
    simpa only [d3415, d2758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3415, d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3415, d2758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29064 (p : Pattern) (guard : d5855 p = 1) : d3416 p ≤ (0 : Int) + d2759 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3416, d2759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29054 p hg
    simpa only [d3416, d2759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3416, d2759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29063 p hg
    simpa only [d3416, d2759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29065 (p : Pattern) (guard : d5855 p = 1) : d3417 p ≤ (0 : Int) + d2760 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3417, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29048 p hg
    simpa only [d3417, d2760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3417, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29055 p hg
    simpa only [d3417, d2760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29066 (p : Pattern) (guard : d5855 p = 1) : d3396 p ≤ (0 : Int) + d2761 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3396, d2761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29050 p hg
    simpa only [d3396, d2761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3396, d2761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28844 p hg
    simpa only [d3396, d2761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29067 (p : Pattern) (guard : d5855 p = 1) : d3418 p ≤ (0 : Int) + d2762 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3418, d2762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29065 p hg
    simpa only [d3418, d2762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3418, d2762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29066 p hg
    simpa only [d3418, d2762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29068 (p : Pattern) (guard : d5855 p = 1) : d3398 p ≤ (0 : Int) + d2763 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3398, d2763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29050 p hg
    simpa only [d3398, d2763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3398, d2763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28850 p hg
    simpa only [d3398, d2763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29069 (p : Pattern) (guard : d5855 p = 1) : d3399 p ≤ (0 : Int) + d2764 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3399, d2764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29068 p hg
    simpa only [d3399, d2764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3399, d2764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3399, d2764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29070 (p : Pattern) (guard : d5855 p = 1) : d3419 p ≤ (0 : Int) + d2765 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3419, d2765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29067 p hg
    simpa only [d3419, d2765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3419, d2765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29069 p hg
    simpa only [d3419, d2765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29071 (p : Pattern) (guard : d5855 p = 1) : d3420 p ≤ (0 : Int) + d2766 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3420, d2766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29060 p hg
    simpa only [d3420, d2766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3420, d2766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3420, d2766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29072 (p : Pattern) (guard : d5855 p = 1) : d3421 p ≤ (0 : Int) + d2767 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3421, d2767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29071 p hg
    simpa only [d3421, d2767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3421, d2767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3421, d2767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29073 (p : Pattern) (guard : d5855 p = 1) : d3422 p ≤ (0 : Int) + d2768 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3422, d2768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29072 p hg
    simpa only [d3422, d2768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3422, d2768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3422, d2768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29074 (p : Pattern) (guard : d5855 p = 1) : d3423 p ≤ (0 : Int) + d2769 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3423, d2769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29070 p hg
    simpa only [d3423, d2769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3423, d2769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29073 p hg
    simpa only [d3423, d2769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29075 (p : Pattern) (guard : d5855 p = 1) : d3424 p ≤ (0 : Int) + d2770 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3424, d2770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29064 p hg
    simpa only [d3424, d2770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3424, d2770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29074 p hg
    simpa only [d3424, d2770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29076 (p : Pattern) (guard : d5855 p = 1) : d3425 p ≤ (0 : Int) + d2771 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3425, d2771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29046 p hg
    simpa only [d3425, d2771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3425, d2771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29075 p hg
    simpa only [d3425, d2771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29077 (p : Pattern) (guard : d5855 p = 1) : d3426 p ≤ (0 : Int) + d2772 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3426, d2772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28988 p hg
    simpa only [d3426, d2772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3426, d2772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3426, d2772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29078 (p : Pattern) (guard : d5855 p = 1) : d3427 p ≤ (0 : Int) + d2773 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3427, d2773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29077 p hg
    simpa only [d3427, d2773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3427, d2773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3427, d2773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29079 (p : Pattern) (guard : d5855 p = 1) : d3428 p ≤ (0 : Int) + d2774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3428, d2774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29078 p hg
    simpa only [d3428, d2774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3428, d2774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3428, d2774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29080 (p : Pattern) (guard : d5855 p = 1) : d3429 p ≤ (0 : Int) + d2775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3429, d2775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29079 p hg
    simpa only [d3429, d2775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3429, d2775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3429, d2775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29081 (p : Pattern) (guard : d5855 p = 1) : d3430 p ≤ (0 : Int) + d2776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3430, d2776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29075 p hg
    simpa only [d3430, d2776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3430, d2776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29080 p hg
    simpa only [d3430, d2776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29082 (p : Pattern) (guard : d5855 p = 1) : d3431 p ≤ (0 : Int) + d2777 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3431, d2777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29076 p hg
    simpa only [d3431, d2777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3431, d2777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29081 p hg
    simpa only [d3431, d2777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29083 (p : Pattern) (guard : d5855 p = 1) : d3410 p ≤ (0 : Int) + d2778 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3410, d2778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28967 p hg
    simpa only [d3410, d2778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3410, d2778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28986 p hg
    simpa only [d3410, d2778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29084 (p : Pattern) (guard : d5855 p = 1) : d3411 p ≤ (0 : Int) + d2779 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3411, d2779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29083 p hg
    simpa only [d3411, d2779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3411, d2779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28989 p hg
    simpa only [d3411, d2779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29085 (p : Pattern) (guard : d5855 p = 1) : d3432 p ≤ (0 : Int) + d2780 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3432, d2780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29084 p hg
    simpa only [d3432, d2780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3432, d2780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29014 p hg
    simpa only [d3432, d2780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29086 (p : Pattern) (guard : d5855 p = 1) : d3417 p ≤ (0 : Int) + d2781 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3417, d2781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28967 p hg
    simpa only [d3417, d2781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3417, d2781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29031 p hg
    simpa only [d3417, d2781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29087 (p : Pattern) (guard : d5855 p = 1) : d3418 p ≤ (0 : Int) + d2782 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3418, d2782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29086 p hg
    simpa only [d3418, d2782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3418, d2782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29033 p hg
    simpa only [d3418, d2782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29088 (p : Pattern) (guard : d5855 p = 1) : d3419 p ≤ (0 : Int) + d2783 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3419, d2783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29087 p hg
    simpa only [d3419, d2783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3419, d2783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29036 p hg
    simpa only [d3419, d2783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29089 (p : Pattern) (guard : d5855 p = 1) : d3433 p ≤ (0 : Int) + d2784 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3433, d2784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29088 p hg
    simpa only [d3433, d2784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3433, d2784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29044 p hg
    simpa only [d3433, d2784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29090 (p : Pattern) (guard : d5855 p = 1) : d3434 p ≤ (0 : Int) + d2785 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3434, d2785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29085 p hg
    simpa only [d3434, d2785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3434, d2785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29089 p hg
    simpa only [d3434, d2785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29091 (p : Pattern) (guard : d5855 p = 1) : d3435 p ≤ (0 : Int) + d2786 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3435, d2786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29090 p hg
    simpa only [d3435, d2786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3435, d2786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29075 p hg
    simpa only [d3435, d2786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29092 (p : Pattern) (guard : d5855 p = 1) : d3436 p ≤ (0 : Int) + d2787 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3436, d2787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29075 p hg
    simpa only [d3436, d2787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3436, d2787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3436, d2787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29093 (p : Pattern) (guard : d5855 p = 1) : d3437 p ≤ (0 : Int) + d2788 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3437, d2788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29091 p hg
    simpa only [d3437, d2788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3437, d2788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29092 p hg
    simpa only [d3437, d2788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29094 (p : Pattern) (guard : d5855 p = 1) : d3438 p ≤ (0 : Int) + d2789 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3438, d2789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29082 p hg
    simpa only [d3438, d2789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3438, d2789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29093 p hg
    simpa only [d3438, d2789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29095 (p : Pattern) (guard : d5855 p = 1) : d3439 p ≤ (0 : Int) + d2790 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3439, d2790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28921 p hg
    simpa only [d3439, d2790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3439, d2790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29094 p hg
    simpa only [d3439, d2790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29096 (p : Pattern) (guard : d5855 p = 1) : d3440 p ≤ (0 : Int) + d2791 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3440, d2791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28945 p hg
    simpa only [d3440, d2791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3440, d2791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29095 p hg
    simpa only [d3440, d2791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29097 (p : Pattern) (guard : d5855 p = 1) : d3441 p ≤ (0 : Int) + d2792 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3441, d2792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28825 p hg
    simpa only [d3441, d2792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3441, d2792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28799 p hg
    simpa only [d3441, d2792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29098 (p : Pattern) (guard : d5855 p = 1) : d3442 p ≤ (0 : Int) + d2793 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3442, d2793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28877 p hg
    simpa only [d3442, d2793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3442, d2793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29097 p hg
    simpa only [d3442, d2793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29099 (p : Pattern) (guard : d5855 p = 1) : d3443 p ≤ (0 : Int) + d2794 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3443, d2794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28825 p hg
    simpa only [d3443, d2794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3443, d2794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28805 p hg
    simpa only [d3443, d2794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29100 (p : Pattern) (guard : d5855 p = 1) : d3444 p ≤ (0 : Int) + d2795 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3444, d2795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28881 p hg
    simpa only [d3444, d2795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3444, d2795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3444, d2795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29101 (p : Pattern) (guard : d5855 p = 1) : d3445 p ≤ (0 : Int) + d2796 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3445, d2796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29099 p hg
    simpa only [d3445, d2796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3445, d2796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29100 p hg
    simpa only [d3445, d2796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29102 (p : Pattern) (guard : d5855 p = 1) : d3446 p ≤ (0 : Int) + d2797 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3446, d2797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29098 p hg
    simpa only [d3446, d2797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3446, d2797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29101 p hg
    simpa only [d3446, d2797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29103 (p : Pattern) (guard : d5855 p = 1) : d3447 p ≤ (0 : Int) + d2798 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3447, d2798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28854 p hg
    simpa only [d3447, d2798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3447, d2798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29100 p hg
    simpa only [d3447, d2798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29104 (p : Pattern) (guard : d5855 p = 1) : d3448 p ≤ (0 : Int) + d2799 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3448, d2799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29103 p hg
    simpa only [d3448, d2799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3448, d2799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28861 p hg
    simpa only [d3448, d2799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29105 (p : Pattern) (guard : d5855 p = 1) : d3449 p ≤ (0 : Int) + d2800 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3449, d2800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29102 p hg
    simpa only [d3449, d2800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3449, d2800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29104 p hg
    simpa only [d3449, d2800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29106 (p : Pattern) (guard : d5855 p = 1) : d3450 p ≤ (0 : Int) + d2801 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3450, d2801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28876 p hg
    simpa only [d3450, d2801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3450, d2801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29105 p hg
    simpa only [d3450, d2801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29107 (p : Pattern) (guard : d5855 p = 1) : d3451 p ≤ (0 : Int) + d2802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3451, d2802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29097 p hg
    simpa only [d3451, d2802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3451, d2802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28807 p hg
    simpa only [d3451, d2802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29108 (p : Pattern) (guard : d5855 p = 1) : d3452 p ≤ (0 : Int) + d2803 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3452, d2803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29100 p hg
    simpa only [d3452, d2803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3452, d2803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28860 p hg
    simpa only [d3452, d2803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29109 (p : Pattern) (guard : d5855 p = 1) : d3453 p ≤ (0 : Int) + d2804 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3453, d2804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29107 p hg
    simpa only [d3453, d2804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3453, d2804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29108 p hg
    simpa only [d3453, d2804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29110 (p : Pattern) (guard : d5855 p = 1) : d3454 p ≤ (0 : Int) + d2805 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3454, d2805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29100 p hg
    simpa only [d3454, d2805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3454, d2805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3454, d2805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29111 (p : Pattern) (guard : d5855 p = 1) : d3455 p ≤ (0 : Int) + d2806 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3455, d2806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29110 p hg
    simpa only [d3455, d2806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3455, d2806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3455, d2806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29112 (p : Pattern) (guard : d5855 p = 1) : d3456 p ≤ (0 : Int) + d2807 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3456, d2807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29109 p hg
    simpa only [d3456, d2807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3456, d2807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29111 p hg
    simpa only [d3456, d2807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29113 (p : Pattern) (guard : d5855 p = 1) : d3457 p ≤ (0 : Int) + d2808 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3457, d2808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28892 p hg
    simpa only [d3457, d2808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3457, d2808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29112 p hg
    simpa only [d3457, d2808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29114 (p : Pattern) (guard : d5855 p = 1) : d3458 p ≤ (0 : Int) + d2809 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3458, d2809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29106 p hg
    simpa only [d3458, d2809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3458, d2809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29113 p hg
    simpa only [d3458, d2809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29115 (p : Pattern) (guard : d5855 p = 1) : d3459 p ≤ (0 : Int) + d2810 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3459, d2810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28867 p hg
    simpa only [d3459, d2810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3459, d2810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28883 p hg
    simpa only [d3459, d2810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29116 (p : Pattern) (guard : d5855 p = 1) : d3460 p ≤ (0 : Int) + d2811 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3460, d2811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29115 p hg
    simpa only [d3460, d2811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3460, d2811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28884 p hg
    simpa only [d3460, d2811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29117 (p : Pattern) (guard : d5851 p = 1) : d3461 p ≤ (0 : Int) + d2812 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5268 p = 1 := by simpa only [d5851, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26891 p hg
    simpa only [d5851, d2812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5851, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26892 p hg
    simpa only [d5851, d2812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29118 (p : Pattern) (guard : d5847 p = 1) : d3461 p ≤ (0 : Int) + d191 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3461, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23780 p hg
    simpa only [d5847, d3461, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3461, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20382 p hg
    simpa only [d5847, d3461, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29119 (p : Pattern) (guard : d5854 p = 1) : d3461 p ≤ (0 : Int) + d2812 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29118 p hg
    simpa only [d5854, d2812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26892 p hg
    simpa only [d5854, d2812, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
