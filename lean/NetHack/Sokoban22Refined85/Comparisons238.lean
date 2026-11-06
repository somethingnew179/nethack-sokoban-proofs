/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons237
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare33320 (p : Pattern) (guard : d5843 p = 1) : d6 p ≤ (2 : Int) + d6 p := by
  omega
theorem compare33321 (p : Pattern) (guard : d5843 p = 1) : d35 p ≤ (2 : Int) + d3253 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d35, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33320 p hg
    simpa only [d35, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d35, d3253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33274 p hg
    simpa only [d35, d3253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33322 (p : Pattern) (guard : d5843 p = 1) : d364 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33274 p hg
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33323 (p : Pattern) (guard : d5843 p = 1) : d1720 p ≤ (2 : Int) + d7693 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1720, d7693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33321 p hg
    simpa only [d1720, d7693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1720, d7693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33322 p hg
    simpa only [d1720, d7693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33324 (p : Pattern) (guard : d0 p = 1) : d10 p ≤ (2 : Int) + d10 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare33325 (p : Pattern) (guard : d5843 p = 1) : d1721 p ≤ (2 : Int) + d10 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24654 p hg
    simpa only [d5843, d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33324 p hg
    simpa only [d5843, d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33326 (p : Pattern) (guard : d5843 p = 1) : d57 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1829 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33327 (p : Pattern) (guard : d5843 p = 1) : d1722 p ≤ (2 : Int) + d3279 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1722, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33325 p hg
    simpa only [d1722, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1722, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33326 p hg
    simpa only [d1722, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33328 (p : Pattern) (guard : d5843 p = 1) : d1723 p ≤ (2 : Int) + d7697 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1723, d7697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33327 p hg
    simpa only [d1723, d7697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1723, d7697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33322 p hg
    simpa only [d1723, d7697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33329 (p : Pattern) (guard : d5843 p = 1) : d1724 p ≤ (2 : Int) + d7698 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1724, d7698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33323 p hg
    simpa only [d1724, d7698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1724, d7698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33328 p hg
    simpa only [d1724, d7698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33330 (p : Pattern) (guard : d5843 p = 1) : d1725 p ≤ (2 : Int) + d7699 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1725, d7699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33329 p hg
    simpa only [d1725, d7699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1725, d7699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d1725, d7699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33331 (p : Pattern) (guard : d5843 p = 1) : d2908 p ≤ (2 : Int) + d7700 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2908, d7700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33307 p hg
    simpa only [d2908, d7700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2908, d7700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33330 p hg
    simpa only [d2908, d7700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33332 (p : Pattern) (guard : d5843 p = 1) : d2909 p ≤ (2 : Int) + d7701 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2909, d7701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33319 p hg
    simpa only [d2909, d7701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2909, d7701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33331 p hg
    simpa only [d2909, d7701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33333 (p : Pattern) (guard : d5843 p = 1) : d11 p ≤ (2 : Int) + d11 p := by
  omega
theorem compare33334 (p : Pattern) (guard : d5843 p = 1) : d40 p ≤ (2 : Int) + d3257 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d40, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33333 p hg
    simpa only [d40, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d40, d3257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33291 p hg
    simpa only [d40, d3257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33335 (p : Pattern) (guard : d5843 p = 1) : d327 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33291 p hg
    simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33336 (p : Pattern) (guard : d5843 p = 1) : d1728 p ≤ (2 : Int) + d7702 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1728, d7702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33334 p hg
    simpa only [d1728, d7702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1728, d7702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33335 p hg
    simpa only [d1728, d7702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33337 (p : Pattern) (guard : d5843 p = 1) : d1729 p ≤ (2 : Int) + d7703 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1729, d7703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33336 p hg
    simpa only [d1729, d7703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1729, d7703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33335 p hg
    simpa only [d1729, d7703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33338 (p : Pattern) (guard : d5843 p = 1) : d1730 p ≤ (2 : Int) + d7704 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1730, d7704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33337 p hg
    simpa only [d1730, d7704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1730, d7704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d1730, d7704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33339 (p : Pattern) (guard : d5843 p = 1) : d2910 p ≤ (2 : Int) + d7705 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2910, d7705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33307 p hg
    simpa only [d2910, d7705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2910, d7705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33338 p hg
    simpa only [d2910, d7705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33340 (p : Pattern) (guard : d5843 p = 1) : d1791 p ≤ (2 : Int) + d10 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4849 p hg
    simpa only [d5843, d1791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33324 p hg
    simpa only [d5843, d1791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33341 (p : Pattern) (guard : d5843 p = 1) : d1792 p ≤ (2 : Int) + d3279 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1792, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33340 p hg
    simpa only [d1792, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1792, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33326 p hg
    simpa only [d1792, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33342 (p : Pattern) (guard : d5843 p = 1) : d1793 p ≤ (2 : Int) + d7706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1793, d7706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33264 p hg
    simpa only [d1793, d7706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1793, d7706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33341 p hg
    simpa only [d1793, d7706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33343 (p : Pattern) (guard : d5843 p = 1) : d339 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33249 p hg
    simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33344 (p : Pattern) (guard : d5843 p = 1) : d1796 p ≤ (2 : Int) + d7707 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1796, d7707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33268 p hg
    simpa only [d1796, d7707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1796, d7707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33343 p hg
    simpa only [d1796, d7707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33345 (p : Pattern) (guard : d5843 p = 1) : d1797 p ≤ (2 : Int) + d7708 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1797, d7708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33342 p hg
    simpa only [d1797, d7708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1797, d7708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33344 p hg
    simpa only [d1797, d7708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33346 (p : Pattern) (guard : d5843 p = 1) : d2911 p ≤ (2 : Int) + d7709 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2911, d7709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33264 p hg
    simpa only [d2911, d7709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2911, d7709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33345 p hg
    simpa only [d2911, d7709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33347 (p : Pattern) (guard : d5843 p = 1) : d2912 p ≤ (2 : Int) + d7710 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2912, d7710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33346 p hg
    simpa only [d2912, d7710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2912, d7710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2912, d7710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33348 (p : Pattern) (guard : d5843 p = 1) : d2913 p ≤ (2 : Int) + d7711 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2913, d7711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33339 p hg
    simpa only [d2913, d7711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2913, d7711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33347 p hg
    simpa only [d2913, d7711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33349 (p : Pattern) (guard : d5843 p = 1) : d2914 p ≤ (2 : Int) + d7712 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2914, d7712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33332 p hg
    simpa only [d2914, d7712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2914, d7712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33348 p hg
    simpa only [d2914, d7712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33350 (p : Pattern) (guard : d5843 p = 1) : d2915 p ≤ (2 : Int) + d7713 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2915, d7713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33307 p hg
    simpa only [d2915, d7713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2915, d7713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2915, d7713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33351 (p : Pattern) (guard : d5843 p = 1) : d2916 p ≤ (2 : Int) + d7714 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2916, d7714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33350 p hg
    simpa only [d2916, d7714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2916, d7714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33347 p hg
    simpa only [d2916, d7714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33352 (p : Pattern) (guard : d5843 p = 1) : d2917 p ≤ (2 : Int) + d7715 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2917, d7715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33288 p hg
    simpa only [d2917, d7715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2917, d7715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2917, d7715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33353 (p : Pattern) (guard : d5843 p = 1) : d2918 p ≤ (2 : Int) + d7716 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2918, d7716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33352 p hg
    simpa only [d2918, d7716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2918, d7716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2918, d7716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33354 (p : Pattern) (guard : d5843 p = 1) : d2919 p ≤ (2 : Int) + d7717 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2919, d7717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33351 p hg
    simpa only [d2919, d7717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2919, d7717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33353 p hg
    simpa only [d2919, d7717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33355 (p : Pattern) (guard : d5843 p = 1) : d2920 p ≤ (2 : Int) + d7718 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2920, d7718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33349 p hg
    simpa only [d2920, d7718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2920, d7718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33354 p hg
    simpa only [d2920, d7718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33356 (p : Pattern) (guard : d5843 p = 1) : d2921 p ≤ (2 : Int) + d7719 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2921, d7719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33299 p hg
    simpa only [d2921, d7719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2921, d7719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33355 p hg
    simpa only [d2921, d7719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33357 (p : Pattern) (guard : d5843 p = 1) : d2029 p ≤ (2 : Int) + d7720 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2029, d7720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33309 p hg
    simpa only [d2029, d7720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2029, d7720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33314 p hg
    simpa only [d2029, d7720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33358 (p : Pattern) (guard : d5843 p = 1) : d2030 p ≤ (2 : Int) + d7721 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2030, d7721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33357 p hg
    simpa only [d2030, d7721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2030, d7721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33314 p hg
    simpa only [d2030, d7721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33359 (p : Pattern) (guard : d5843 p = 1) : d2922 p ≤ (2 : Int) + d7722 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2922, d7722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33309 p hg
    simpa only [d2922, d7722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2922, d7722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33358 p hg
    simpa only [d2922, d7722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33360 (p : Pattern) (guard : d5843 p = 1) : d1742 p ≤ (2 : Int) + d4 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4831 p hg
    simpa only [d5843, d1742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33247 p hg
    simpa only [d5843, d1742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33361 (p : Pattern) (guard : d5843 p = 1) : d1743 p ≤ (2 : Int) + d3239 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1743, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33360 p hg
    simpa only [d1743, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1743, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33249 p hg
    simpa only [d1743, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33362 (p : Pattern) (guard : d5843 p = 1) : d1744 p ≤ (2 : Int) + d7723 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1744, d7723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33309 p hg
    simpa only [d1744, d7723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1744, d7723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33361 p hg
    simpa only [d1744, d7723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33363 (p : Pattern) (guard : d5843 p = 1) : d1745 p ≤ (2 : Int) + d7724 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1745, d7724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33362 p hg
    simpa only [d1745, d7724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1745, d7724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33361 p hg
    simpa only [d1745, d7724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33364 (p : Pattern) (guard : d5843 p = 1) : d1746 p ≤ (2 : Int) + d7725 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1746, d7725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33363 p hg
    simpa only [d1746, d7725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1746, d7725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d1746, d7725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33365 (p : Pattern) (guard : d5843 p = 1) : d2923 p ≤ (2 : Int) + d7726 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2923, d7726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33359 p hg
    simpa only [d2923, d7726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2923, d7726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33364 p hg
    simpa only [d2923, d7726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33366 (p : Pattern) (guard : d5843 p = 1) : d2924 p ≤ (2 : Int) + d7727 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2924, d7727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33262 p hg
    simpa only [d2924, d7727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2924, d7727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33365 p hg
    simpa only [d2924, d7727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33367 (p : Pattern) (guard : d5843 p = 1) : d2925 p ≤ (2 : Int) + d7728 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2925, d7728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33279 p hg
    simpa only [d2925, d7728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2925, d7728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33296 p hg
    simpa only [d2925, d7728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33368 (p : Pattern) (guard : d5843 p = 1) : d2926 p ≤ (2 : Int) + d7729 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2926, d7729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33366 p hg
    simpa only [d2926, d7729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2926, d7729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33367 p hg
    simpa only [d2926, d7729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33369 (p : Pattern) (guard : d5843 p = 1) : d10 p ≤ (2 : Int) + d10 p := by
  omega
theorem compare33370 (p : Pattern) (guard : d5843 p = 1) : d58 p ≤ (2 : Int) + d3279 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d58, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33369 p hg
    simpa only [d58, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d58, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33326 p hg
    simpa only [d58, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33371 (p : Pattern) (guard : d5843 p = 1) : d329 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33326 p hg
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33372 (p : Pattern) (guard : d5843 p = 1) : d1751 p ≤ (2 : Int) + d7697 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1751, d7697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33370 p hg
    simpa only [d1751, d7697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1751, d7697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33371 p hg
    simpa only [d1751, d7697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33373 (p : Pattern) (guard : d5843 p = 1) : d1752 p ≤ (2 : Int) + d7730 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1752, d7730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33372 p hg
    simpa only [d1752, d7730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1752, d7730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33371 p hg
    simpa only [d1752, d7730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33374 (p : Pattern) (guard : d5843 p = 1) : d2927 p ≤ (2 : Int) + d7731 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2927, d7731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33370 p hg
    simpa only [d2927, d7731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2927, d7731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33373 p hg
    simpa only [d2927, d7731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33375 (p : Pattern) (guard : d5843 p = 1) : d1753 p ≤ (2 : Int) + d7732 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1753, d7732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33373 p hg
    simpa only [d1753, d7732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1753, d7732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d1753, d7732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33376 (p : Pattern) (guard : d5843 p = 1) : d2928 p ≤ (2 : Int) + d7733 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2928, d7733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33374 p hg
    simpa only [d2928, d7733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2928, d7733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33375 p hg
    simpa only [d2928, d7733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33377 (p : Pattern) (guard : d5843 p = 1) : d2929 p ≤ (2 : Int) + d7734 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2929, d7734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33279 p hg
    simpa only [d2929, d7734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2929, d7734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33376 p hg
    simpa only [d2929, d7734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33378 (p : Pattern) (guard : d5843 p = 1) : d2930 p ≤ (2 : Int) + d7735 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2930, d7735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33334 p hg
    simpa only [d2930, d7735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2930, d7735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33337 p hg
    simpa only [d2930, d7735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33379 (p : Pattern) (guard : d5843 p = 1) : d2931 p ≤ (2 : Int) + d7736 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2931, d7736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33378 p hg
    simpa only [d2931, d7736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2931, d7736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33338 p hg
    simpa only [d2931, d7736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33380 (p : Pattern) (guard : d5843 p = 1) : d2932 p ≤ (2 : Int) + d7737 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2932, d7737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33379 p hg
    simpa only [d2932, d7737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2932, d7737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2932, d7737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33381 (p : Pattern) (guard : d5843 p = 1) : d2933 p ≤ (2 : Int) + d7738 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2933, d7738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33377 p hg
    simpa only [d2933, d7738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2933, d7738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33380 p hg
    simpa only [d2933, d7738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33382 (p : Pattern) (guard : d5843 p = 1) : d2934 p ≤ (2 : Int) + d7739 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2934, d7739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33368 p hg
    simpa only [d2934, d7739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2934, d7739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33381 p hg
    simpa only [d2934, d7739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33383 (p : Pattern) (guard : d5843 p = 1) : d2935 p ≤ (2 : Int) + d7740 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2935, d7740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33309 p hg
    simpa only [d2935, d7740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2935, d7740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33317 p hg
    simpa only [d2935, d7740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33384 (p : Pattern) (guard : d5843 p = 1) : d2936 p ≤ (2 : Int) + d7741 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2936, d7741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33383 p hg
    simpa only [d2936, d7741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2936, d7741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2936, d7741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33385 (p : Pattern) (guard : d5843 p = 1) : d2937 p ≤ (2 : Int) + d7742 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2937, d7742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33331 p hg
    simpa only [d2937, d7742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2937, d7742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33384 p hg
    simpa only [d2937, d7742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33386 (p : Pattern) (guard : d5843 p = 1) : d2938 p ≤ (2 : Int) + d7743 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2938, d7743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33347 p hg
    simpa only [d2938, d7743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2938, d7743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33352 p hg
    simpa only [d2938, d7743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33387 (p : Pattern) (guard : d5843 p = 1) : d2939 p ≤ (2 : Int) + d7744 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2939, d7744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33385 p hg
    simpa only [d2939, d7744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2939, d7744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33386 p hg
    simpa only [d2939, d7744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33388 (p : Pattern) (guard : d5843 p = 1) : d2940 p ≤ (2 : Int) + d7745 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2940, d7745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33374 p hg
    simpa only [d2940, d7745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2940, d7745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2940, d7745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33389 (p : Pattern) (guard : d5843 p = 1) : d2941 p ≤ (2 : Int) + d7746 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2941, d7746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33347 p hg
    simpa only [d2941, d7746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2941, d7746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33388 p hg
    simpa only [d2941, d7746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33390 (p : Pattern) (guard : d5843 p = 1) : d2942 p ≤ (2 : Int) + d7747 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2942, d7747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33378 p hg
    simpa only [d2942, d7747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2942, d7747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2942, d7747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33391 (p : Pattern) (guard : d5843 p = 1) : d2943 p ≤ (2 : Int) + d7748 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2943, d7748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33390 p hg
    simpa only [d2943, d7748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2943, d7748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2943, d7748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33392 (p : Pattern) (guard : d5843 p = 1) : d2944 p ≤ (2 : Int) + d7749 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2944, d7749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33389 p hg
    simpa only [d2944, d7749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2944, d7749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33391 p hg
    simpa only [d2944, d7749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33393 (p : Pattern) (guard : d5843 p = 1) : d2945 p ≤ (2 : Int) + d7750 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2945, d7750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33387 p hg
    simpa only [d2945, d7750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2945, d7750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33392 p hg
    simpa only [d2945, d7750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33394 (p : Pattern) (guard : d5843 p = 1) : d2946 p ≤ (2 : Int) + d7751 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2946, d7751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33382 p hg
    simpa only [d2946, d7751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2946, d7751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33393 p hg
    simpa only [d2946, d7751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33395 (p : Pattern) (guard : d5843 p = 1) : d2947 p ≤ (2 : Int) + d7752 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2947, d7752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33356 p hg
    simpa only [d2947, d7752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2947, d7752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33394 p hg
    simpa only [d2947, d7752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33396 (p : Pattern) (guard : d5843 p = 1) : d2047 p ≤ (2 : Int) + d7672 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2047, d7672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33250 p hg
    simpa only [d2047, d7672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2047, d7672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33301 p hg
    simpa only [d2047, d7672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33397 (p : Pattern) (guard : d5843 p = 1) : d2048 p ≤ (2 : Int) + d7753 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2048, d7753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33302 p hg
    simpa only [d2048, d7753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2048, d7753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33396 p hg
    simpa only [d2048, d7753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33398 (p : Pattern) (guard : d5843 p = 1) : d2948 p ≤ (2 : Int) + d7754 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2948, d7754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33246 p hg
    simpa only [d2948, d7754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2948, d7754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33397 p hg
    simpa only [d2948, d7754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33399 (p : Pattern) (guard : d5843 p = 1) : d1773 p ≤ (2 : Int) + d7755 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1773, d7755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33252 p hg
    simpa only [d1773, d7755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1773, d7755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d1773, d7755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33400 (p : Pattern) (guard : d5843 p = 1) : d2949 p ≤ (2 : Int) + d7756 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2949, d7756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33398 p hg
    simpa only [d2949, d7756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2949, d7756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33399 p hg
    simpa only [d2949, d7756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33401 (p : Pattern) (guard : d5843 p = 1) : d2051 p ≤ (2 : Int) + d10 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d2051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32225 p hg
    simpa only [d5843, d2051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d2051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33324 p hg
    simpa only [d5843, d2051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33402 (p : Pattern) (guard : d5843 p = 1) : d2052 p ≤ (2 : Int) + d3279 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2052, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33401 p hg
    simpa only [d2052, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2052, d3279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33283 p hg
    simpa only [d2052, d3279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33403 (p : Pattern) (guard : d5843 p = 1) : d2053 p ≤ (2 : Int) + d7706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2053, d7706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33250 p hg
    simpa only [d2053, d7706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2053, d7706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33402 p hg
    simpa only [d2053, d7706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33404 (p : Pattern) (guard : d5843 p = 1) : d2054 p ≤ (2 : Int) + d7757 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2054, d7757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33302 p hg
    simpa only [d2054, d7757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2054, d7757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33403 p hg
    simpa only [d2054, d7757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33405 (p : Pattern) (guard : d5843 p = 1) : d2950 p ≤ (2 : Int) + d7758 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2950, d7758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33246 p hg
    simpa only [d2950, d7758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2950, d7758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33404 p hg
    simpa only [d2950, d7758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33406 (p : Pattern) (guard : d5843 p = 1) : d1778 p ≤ (2 : Int) + d8 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16112 p hg
    simpa only [d5843, d1778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33265 p hg
    simpa only [d5843, d1778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33407 (p : Pattern) (guard : d5843 p = 1) : d1779 p ≤ (2 : Int) + d3461 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1779, d3461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33406 p hg
    simpa only [d1779, d3461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1779, d3461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33267 p hg
    simpa only [d1779, d3461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33408 (p : Pattern) (guard : d5843 p = 1) : d1780 p ≤ (2 : Int) + d7669 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1780, d7669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33250 p hg
    simpa only [d1780, d7669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1780, d7669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33407 p hg
    simpa only [d1780, d7669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33409 (p : Pattern) (guard : d5843 p = 1) : d1781 p ≤ (2 : Int) + d7759 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1781, d7759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33302 p hg
    simpa only [d1781, d7759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1781, d7759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33408 p hg
    simpa only [d1781, d7759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33410 (p : Pattern) (guard : d5843 p = 1) : d1782 p ≤ (2 : Int) + d7760 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1782, d7760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33409 p hg
    simpa only [d1782, d7760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1782, d7760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d1782, d7760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33411 (p : Pattern) (guard : d5843 p = 1) : d2951 p ≤ (2 : Int) + d7761 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2951, d7761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33405 p hg
    simpa only [d2951, d7761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2951, d7761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33410 p hg
    simpa only [d2951, d7761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33412 (p : Pattern) (guard : d5843 p = 1) : d2952 p ≤ (2 : Int) + d7762 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2952, d7762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33400 p hg
    simpa only [d2952, d7762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2952, d7762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33411 p hg
    simpa only [d2952, d7762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33413 (p : Pattern) (guard : d5843 p = 1) : d1789 p ≤ (2 : Int) + d7763 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1789, d7763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33306 p hg
    simpa only [d1789, d7763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1789, d7763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d1789, d7763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33414 (p : Pattern) (guard : d5843 p = 1) : d2953 p ≤ (2 : Int) + d7764 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2953, d7764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33307 p hg
    simpa only [d2953, d7764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2953, d7764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33413 p hg
    simpa only [d2953, d7764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33415 (p : Pattern) (guard : d5843 p = 1) : d1798 p ≤ (2 : Int) + d7765 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1798, d7765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33345 p hg
    simpa only [d1798, d7765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1798, d7765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d1798, d7765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33416 (p : Pattern) (guard : d5843 p = 1) : d2954 p ≤ (2 : Int) + d7766 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2954, d7766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33346 p hg
    simpa only [d2954, d7766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2954, d7766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33415 p hg
    simpa only [d2954, d7766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33417 (p : Pattern) (guard : d5843 p = 1) : d2955 p ≤ (2 : Int) + d7767 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2955, d7767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33414 p hg
    simpa only [d2955, d7767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2955, d7767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33416 p hg
    simpa only [d2955, d7767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33418 (p : Pattern) (guard : d5843 p = 1) : d2956 p ≤ (2 : Int) + d7768 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2956, d7768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33412 p hg
    simpa only [d2956, d7768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2956, d7768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33417 p hg
    simpa only [d2956, d7768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33419 (p : Pattern) (guard : d5843 p = 1) : d1804 p ≤ (2 : Int) + d7769 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d1804, d7769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33287 p hg
    simpa only [d1804, d7769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d1804, d7769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d1804, d7769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33420 (p : Pattern) (guard : d5843 p = 1) : d2957 p ≤ (2 : Int) + d7770 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2957, d7770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33288 p hg
    simpa only [d2957, d7770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2957, d7770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33419 p hg
    simpa only [d2957, d7770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33421 (p : Pattern) (guard : d5843 p = 1) : d2958 p ≤ (2 : Int) + d7771 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2958, d7771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33420 p hg
    simpa only [d2958, d7771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2958, d7771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2958, d7771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33422 (p : Pattern) (guard : d5843 p = 1) : d2959 p ≤ (2 : Int) + d7772 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2959, d7772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33417 p hg
    simpa only [d2959, d7772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2959, d7772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33421 p hg
    simpa only [d2959, d7772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33423 (p : Pattern) (guard : d5843 p = 1) : d2960 p ≤ (2 : Int) + d7773 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2960, d7773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33418 p hg
    simpa only [d2960, d7773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2960, d7773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33422 p hg
    simpa only [d2960, d7773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33424 (p : Pattern) (guard : d5843 p = 1) : d2961 p ≤ (2 : Int) + d7774 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2961, d7774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33383 p hg
    simpa only [d2961, d7774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2961, d7774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33318 p hg
    simpa only [d2961, d7774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33425 (p : Pattern) (guard : d5843 p = 1) : d2962 p ≤ (2 : Int) + d7775 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2962, d7775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33321 p hg
    simpa only [d2962, d7775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2962, d7775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33329 p hg
    simpa only [d2962, d7775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33426 (p : Pattern) (guard : d5843 p = 1) : d2963 p ≤ (2 : Int) + d7776 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2963, d7776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33425 p hg
    simpa only [d2963, d7776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2963, d7776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33330 p hg
    simpa only [d2963, d7776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33427 (p : Pattern) (guard : d5843 p = 1) : d2964 p ≤ (2 : Int) + d7777 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2964, d7777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33424 p hg
    simpa only [d2964, d7777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2964, d7777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33426 p hg
    simpa only [d2964, d7777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33428 (p : Pattern) (guard : d5843 p = 1) : d2965 p ≤ (2 : Int) + d7778 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2965, d7778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33427 p hg
    simpa only [d2965, d7778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2965, d7778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33380 p hg
    simpa only [d2965, d7778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33429 (p : Pattern) (guard : d5843 p = 1) : d2966 p ≤ (2 : Int) + d7779 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2966, d7779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33428 p hg
    simpa only [d2966, d7779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2966, d7779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2966, d7779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33430 (p : Pattern) (guard : d5843 p = 1) : d2967 p ≤ (2 : Int) + d7780 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2967, d7780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33423 p hg
    simpa only [d2967, d7780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2967, d7780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33429 p hg
    simpa only [d2967, d7780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33431 (p : Pattern) (guard : d5843 p = 1) : d2968 p ≤ (2 : Int) + d7781 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2968, d7781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33411 p hg
    simpa only [d2968, d7781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2968, d7781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33424 p hg
    simpa only [d2968, d7781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33432 (p : Pattern) (guard : d5843 p = 1) : d2969 p ≤ (2 : Int) + d7782 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2969, d7782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33416 p hg
    simpa only [d2969, d7782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2969, d7782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33420 p hg
    simpa only [d2969, d7782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33433 (p : Pattern) (guard : d5843 p = 1) : d2970 p ≤ (2 : Int) + d7783 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2970, d7783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33431 p hg
    simpa only [d2970, d7783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2970, d7783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33432 p hg
    simpa only [d2970, d7783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33434 (p : Pattern) (guard : d5843 p = 1) : d2971 p ≤ (2 : Int) + d7784 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2971, d7784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33416 p hg
    simpa only [d2971, d7784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2971, d7784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33376 p hg
    simpa only [d2971, d7784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33435 (p : Pattern) (guard : d5843 p = 1) : d2972 p ≤ (2 : Int) + d7785 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2972, d7785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33434 p hg
    simpa only [d2972, d7785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2972, d7785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33380 p hg
    simpa only [d2972, d7785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33436 (p : Pattern) (guard : d5843 p = 1) : d2973 p ≤ (2 : Int) + d7786 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2973, d7786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33433 p hg
    simpa only [d2973, d7786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2973, d7786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33435 p hg
    simpa only [d2973, d7786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33437 (p : Pattern) (guard : d5843 p = 1) : d2974 p ≤ (2 : Int) + d7787 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2974, d7787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33426 p hg
    simpa only [d2974, d7787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2974, d7787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2974, d7787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33438 (p : Pattern) (guard : d5843 p = 1) : d2975 p ≤ (2 : Int) + d7788 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2975, d7788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33437 p hg
    simpa only [d2975, d7788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2975, d7788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2975, d7788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33439 (p : Pattern) (guard : d5843 p = 1) : d2976 p ≤ (2 : Int) + d7789 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2976, d7789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33438 p hg
    simpa only [d2976, d7789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2976, d7789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2976, d7789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33440 (p : Pattern) (guard : d5843 p = 1) : d2977 p ≤ (2 : Int) + d7790 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2977, d7790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33436 p hg
    simpa only [d2977, d7790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2977, d7790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33439 p hg
    simpa only [d2977, d7790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33441 (p : Pattern) (guard : d5843 p = 1) : d2978 p ≤ (2 : Int) + d7791 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2978, d7791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33430 p hg
    simpa only [d2978, d7791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2978, d7791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33440 p hg
    simpa only [d2978, d7791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33442 (p : Pattern) (guard : d5843 p = 1) : d2979 p ≤ (2 : Int) + d7792 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2979, d7792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33395 p hg
    simpa only [d2979, d7792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2979, d7792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33441 p hg
    simpa only [d2979, d7792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33443 (p : Pattern) (guard : d5843 p = 1) : d2980 p ≤ (2 : Int) + d7793 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2980, d7793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33420 p hg
    simpa only [d2980, d7793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2980, d7793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33379 p hg
    simpa only [d2980, d7793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33444 (p : Pattern) (guard : d5843 p = 1) : d2981 p ≤ (2 : Int) + d7794 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2981, d7794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33443 p hg
    simpa only [d2981, d7794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2981, d7794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33380 p hg
    simpa only [d2981, d7794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33445 (p : Pattern) (guard : d5843 p = 1) : d2982 p ≤ (2 : Int) + d7795 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2982, d7795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33380 p hg
    simpa only [d2982, d7795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2982, d7795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2982, d7795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33446 (p : Pattern) (guard : d5843 p = 1) : d2983 p ≤ (2 : Int) + d7796 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2983, d7796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33444 p hg
    simpa only [d2983, d7796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2983, d7796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33445 p hg
    simpa only [d2983, d7796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33447 (p : Pattern) (guard : d5843 p = 1) : d2984 p ≤ (2 : Int) + d7797 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2984, d7797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33445 p hg
    simpa only [d2984, d7797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2984, d7797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2984, d7797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33448 (p : Pattern) (guard : d5843 p = 1) : d2985 p ≤ (2 : Int) + d7798 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2985, d7798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33446 p hg
    simpa only [d2985, d7798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2985, d7798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33447 p hg
    simpa only [d2985, d7798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33449 (p : Pattern) (guard : d5843 p = 1) : d2986 p ≤ (2 : Int) + d7799 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2986, d7799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33447 p hg
    simpa only [d2986, d7799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2986, d7799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2986, d7799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33450 (p : Pattern) (guard : d5843 p = 1) : d2987 p ≤ (2 : Int) + d7800 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2987, d7800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33448 p hg
    simpa only [d2987, d7800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2987, d7800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33449 p hg
    simpa only [d2987, d7800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33451 (p : Pattern) (guard : d5843 p = 1) : d2988 p ≤ (2 : Int) + d7801 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2988, d7801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33441 p hg
    simpa only [d2988, d7801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2988, d7801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33450 p hg
    simpa only [d2988, d7801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33452 (p : Pattern) (guard : d5843 p = 1) : d2989 p ≤ (2 : Int) + d7802 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2989, d7802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33442 p hg
    simpa only [d2989, d7802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2989, d7802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33451 p hg
    simpa only [d2989, d7802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33453 (p : Pattern) (guard : d5843 p = 1) : d2990 p ≤ (2 : Int) + d7803 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2990, d7803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33441 p hg
    simpa only [d2990, d7803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2990, d7803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33260 p hg
    simpa only [d2990, d7803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33454 (p : Pattern) (guard : d5843 p = 1) : d2991 p ≤ (2 : Int) + d7804 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2991, d7804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33442 p hg
    simpa only [d2991, d7804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2991, d7804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33453 p hg
    simpa only [d2991, d7804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33455 (p : Pattern) (guard : d5843 p = 1) : d2992 p ≤ (2 : Int) + d7805 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d2992, d7805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33452 p hg
    simpa only [d2992, d7805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d2992, d7805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33454 p hg
    simpa only [d2992, d7805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33456 (p : Pattern) (guard : d5843 p = 1) : d1 p ≤ (2 : Int) + d1 p := by
  omega
theorem compare33457 (p : Pattern) (guard : d5843 p = 1) : d102 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15997 p hg
    simpa only [d5843, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d5843, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33458 (p : Pattern) (guard : d5843 p = 1) : d103 p ≤ (2 : Int) + d3358 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d103, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33456 p hg
    simpa only [d103, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d103, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33457 p hg
    simpa only [d103, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33459 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (2 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
