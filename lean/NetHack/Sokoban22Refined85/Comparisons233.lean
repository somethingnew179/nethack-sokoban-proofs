/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons232
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare32620 (p : Pattern) (guard : d4474 p = 1) : d3194 p ≤ (2 : Int) + d7219 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3194, d7219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32587 p hg
    simpa only [d3194, d7219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3194, d7219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32619 p hg
    simpa only [d3194, d7219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32621 (p : Pattern) (guard : d4474 p = 1) : d3195 p ≤ (2 : Int) + d7220 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3195, d7220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32400 p hg
    simpa only [d3195, d7220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3195, d7220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32402 p hg
    simpa only [d3195, d7220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32622 (p : Pattern) (guard : d4474 p = 1) : d3196 p ≤ (2 : Int) + d7221 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3196, d7221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32408 p hg
    simpa only [d3196, d7221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3196, d7221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32192 p hg
    simpa only [d3196, d7221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32623 (p : Pattern) (guard : d4474 p = 1) : d3197 p ≤ (2 : Int) + d7222 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3197, d7222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32621 p hg
    simpa only [d3197, d7222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3197, d7222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32622 p hg
    simpa only [d3197, d7222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32624 (p : Pattern) (guard : d4474 p = 1) : d3198 p ≤ (2 : Int) + d7223 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3198, d7223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32623 p hg
    simpa only [d3198, d7223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3198, d7223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32427 p hg
    simpa only [d3198, d7223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32625 (p : Pattern) (guard : d4474 p = 1) : d3199 p ≤ (2 : Int) + d7224 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3199, d7224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32624 p hg
    simpa only [d3199, d7224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3199, d7224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32431 p hg
    simpa only [d3199, d7224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32626 (p : Pattern) (guard : d1 p = 1) : d2154 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d2154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1755 p hg
    simpa only [d2154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32627 (p : Pattern) (guard : d1 p = 1) : d2155 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32626 p hg
    simpa only [d2155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1756 p hg
    simpa only [d2155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32628 (p : Pattern) (guard : d1 p = 1) : d2156 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16033 p hg
    simpa only [d2156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32627 p hg
    simpa only [d2156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32629 (p : Pattern) (guard : d1 p = 1) : d2157 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16031 p hg
    simpa only [d2157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32628 p hg
    simpa only [d2157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32630 (p : Pattern) (guard : d4474 p = 1) : d2158 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32629 p hg
    simpa only [d4474, d2158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d2158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32631 (p : Pattern) (guard : d4474 p = 1) : d3200 p ≤ (2 : Int) + d7101 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3200, d7101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32371 p hg
    simpa only [d3200, d7101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3200, d7101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32630 p hg
    simpa only [d3200, d7101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32632 (p : Pattern) (guard : d4474 p = 1) : d3201 p ≤ (2 : Int) + d7101 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32631 p hg
    simpa only [d3201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32408 p hg
    simpa only [d3201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32633 (p : Pattern) (guard : d4474 p = 1) : d3202 p ≤ (2 : Int) + d7206 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3202, d7206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32632 p hg
    simpa only [d3202, d7206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3202, d7206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32554 p hg
    simpa only [d3202, d7206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32634 (p : Pattern) (guard : d4474 p = 1) : d3203 p ≤ (2 : Int) + d7207 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3203, d7207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32633 p hg
    simpa only [d3203, d7207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3203, d7207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32430 p hg
    simpa only [d3203, d7207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32635 (p : Pattern) (guard : d4474 p = 1) : d3204 p ≤ (2 : Int) + d7216 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3204, d7216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32244 p hg
    simpa only [d3204, d7216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3204, d7216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3204, d7216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32636 (p : Pattern) (guard : d4474 p = 1) : d3205 p ≤ (2 : Int) + d7225 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3205, d7225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32635 p hg
    simpa only [d3205, d7225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3205, d7225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3205, d7225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32637 (p : Pattern) (guard : d4474 p = 1) : d3206 p ≤ (2 : Int) + d7226 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3206, d7226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32634 p hg
    simpa only [d3206, d7226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3206, d7226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32636 p hg
    simpa only [d3206, d7226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32638 (p : Pattern) (guard : d4474 p = 1) : d3207 p ≤ (2 : Int) + d7227 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3207, d7227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32625 p hg
    simpa only [d3207, d7227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3207, d7227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32637 p hg
    simpa only [d3207, d7227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32639 (p : Pattern) (guard : d4474 p = 1) : d3208 p ≤ (2 : Int) + d7228 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3208, d7228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32620 p hg
    simpa only [d3208, d7228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3208, d7228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32638 p hg
    simpa only [d3208, d7228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32640 (p : Pattern) (guard : d4474 p = 1) : d3209 p ≤ (2 : Int) + d7229 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3209, d7229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32408 p hg
    simpa only [d3209, d7229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3209, d7229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32243 p hg
    simpa only [d3209, d7229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32641 (p : Pattern) (guard : d4474 p = 1) : d3210 p ≤ (2 : Int) + d7230 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3210, d7230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32621 p hg
    simpa only [d3210, d7230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3210, d7230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32640 p hg
    simpa only [d3210, d7230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32642 (p : Pattern) (guard : d4474 p = 1) : d3211 p ≤ (2 : Int) + d7231 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3211, d7231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32403 p hg
    simpa only [d3211, d7231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3211, d7231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32243 p hg
    simpa only [d3211, d7231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32643 (p : Pattern) (guard : d4474 p = 1) : d3212 p ≤ (2 : Int) + d7232 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3212, d7232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32642 p hg
    simpa only [d3212, d7232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3212, d7232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3212, d7232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32644 (p : Pattern) (guard : d4474 p = 1) : d3213 p ≤ (2 : Int) + d7233 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3213, d7233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32641 p hg
    simpa only [d3213, d7233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3213, d7233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32643 p hg
    simpa only [d3213, d7233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32645 (p : Pattern) (guard : d4474 p = 1) : d3214 p ≤ (2 : Int) + d7234 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3214, d7234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32418 p hg
    simpa only [d3214, d7234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3214, d7234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32192 p hg
    simpa only [d3214, d7234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32646 (p : Pattern) (guard : d4474 p = 1) : d3215 p ≤ (2 : Int) + d7235 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3215, d7235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32645 p hg
    simpa only [d3215, d7235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3215, d7235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3215, d7235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32647 (p : Pattern) (guard : d4474 p = 1) : d3216 p ≤ (2 : Int) + d7236 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3216, d7236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32646 p hg
    simpa only [d3216, d7236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3216, d7236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3216, d7236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32648 (p : Pattern) (guard : d4474 p = 1) : d3217 p ≤ (2 : Int) + d7237 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3217, d7237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32644 p hg
    simpa only [d3217, d7237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3217, d7237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32647 p hg
    simpa only [d3217, d7237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32649 (p : Pattern) (guard : d4474 p = 1) : d3218 p ≤ (2 : Int) + d7238 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3218, d7238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32648 p hg
    simpa only [d3218, d7238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3218, d7238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32637 p hg
    simpa only [d3218, d7238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32650 (p : Pattern) (guard : d4474 p = 1) : d3219 p ≤ (2 : Int) + d7239 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3219, d7239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32649 p hg
    simpa only [d3219, d7239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3219, d7239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d3219, d7239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32651 (p : Pattern) (guard : d4474 p = 1) : d3220 p ≤ (2 : Int) + d7240 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3220, d7240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32639 p hg
    simpa only [d3220, d7240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3220, d7240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32650 p hg
    simpa only [d3220, d7240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32652 (p : Pattern) (guard : d4474 p = 1) : d3221 p ≤ (2 : Int) + d7241 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3221, d7241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32562 p hg
    simpa only [d3221, d7241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3221, d7241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32651 p hg
    simpa only [d3221, d7241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32653 (p : Pattern) (guard : d4474 p = 1) : d3222 p ≤ (2 : Int) + d7242 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3222, d7242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32286 p hg
    simpa only [d3222, d7242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3222, d7242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32652 p hg
    simpa only [d3222, d7242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32654 (p : Pattern) (guard : d4474 p = 1) : d3223 p ≤ (2 : Int) + d7243 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3223, d7243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32543 p hg
    simpa only [d3223, d7243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3223, d7243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32653 p hg
    simpa only [d3223, d7243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32655 (p : Pattern) (guard : d4474 p = 1) : d3224 p ≤ (2 : Int) + d7244 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d3224, d7244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32445 p hg
    simpa only [d3224, d7244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d3224, d7244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32654 p hg
    simpa only [d3224, d7244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32656 (p : Pattern) (guard : d5842 p = 1) : d0 p ≤ (2 : Int) + d0 p := by
  omega
theorem compare32657 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (2 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32658 (p : Pattern) (guard : d6558 p = 1) : d14 p ≤ (2 : Int) + d0 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32656 p hg
    simpa only [d6558, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32657 p hg
    simpa only [d6558, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32659 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (2 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32660 (p : Pattern) (guard : d5842 p = 1) : d1769 p ≤ (2 : Int) + d4 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32659 p hg
    simpa only [d5842, d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15683 p hg
    simpa only [d5842, d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32661 (p : Pattern) (guard : d0 p = 1) : d17 p ≤ (2 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32662 (p : Pattern) (guard : d6558 p = 1) : d1770 p ≤ (2 : Int) + d4 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32660 p hg
    simpa only [d6558, d1770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32661 p hg
    simpa only [d6558, d1770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32663 (p : Pattern) (guard : d6558 p = 1) : d1771 p ≤ (2 : Int) + d7245 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1771, d7245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32658 p hg
    simpa only [d1771, d7245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1771, d7245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32662 p hg
    simpa only [d1771, d7245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32664 (p : Pattern) (guard : d6558 p = 1) : d1772 p ≤ (2 : Int) + d7246 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1772, d7246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32663 p hg
    simpa only [d1772, d7246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1772, d7246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32662 p hg
    simpa only [d1772, d7246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32665 (p : Pattern) (guard : d6558 p = 1) : d2895 p ≤ (2 : Int) + d7247 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2895, d7247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32658 p hg
    simpa only [d2895, d7247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2895, d7247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32664 p hg
    simpa only [d2895, d7247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32666 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (2 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32667 (p : Pattern) (guard : d5842 p = 1) : d1683 p ≤ (2 : Int) + d2 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32666 p hg
    simpa only [d5842, d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15711 p hg
    simpa only [d5842, d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32668 (p : Pattern) (guard : d0 p = 1) : d30 p ≤ (2 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32669 (p : Pattern) (guard : d6558 p = 1) : d1684 p ≤ (2 : Int) + d2 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32667 p hg
    simpa only [d6558, d1684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32668 p hg
    simpa only [d6558, d1684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32670 (p : Pattern) (guard : d6558 p = 1) : d1685 p ≤ (2 : Int) + d7248 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1685, d7248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32658 p hg
    simpa only [d1685, d7248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1685, d7248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32669 p hg
    simpa only [d1685, d7248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32671 (p : Pattern) (guard : d6558 p = 1) : d1686 p ≤ (2 : Int) + d7249 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1686, d7249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32670 p hg
    simpa only [d1686, d7249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1686, d7249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32669 p hg
    simpa only [d1686, d7249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32672 (p : Pattern) (guard : d6558 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare32673 (p : Pattern) (guard : d6558 p = 1) : d1687 p ≤ (2 : Int) + d7250 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1687, d7250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32671 p hg
    simpa only [d1687, d7250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1687, d7250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d1687, d7250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32674 (p : Pattern) (guard : d6558 p = 1) : d2896 p ≤ (2 : Int) + d7251 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2896, d7251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32665 p hg
    simpa only [d2896, d7251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2896, d7251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32673 p hg
    simpa only [d2896, d7251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32675 (p : Pattern) (guard : d5842 p = 1) : d4 p ≤ (2 : Int) + d4 p := by
  omega
theorem compare32676 (p : Pattern) (guard : d6558 p = 1) : d18 p ≤ (2 : Int) + d4 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32675 p hg
    simpa only [d6558, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32661 p hg
    simpa only [d6558, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32677 (p : Pattern) (guard : d0 p = 1) : d4 p ≤ (2 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32678 (p : Pattern) (guard : d5842 p = 1) : d1794 p ≤ (2 : Int) + d8 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32677 p hg
    simpa only [d5842, d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16154 p hg
    simpa only [d5842, d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32679 (p : Pattern) (guard : d0 p = 1) : d190 p ≤ (2 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32680 (p : Pattern) (guard : d6558 p = 1) : d1795 p ≤ (2 : Int) + d8 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32678 p hg
    simpa only [d6558, d1795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32679 p hg
    simpa only [d6558, d1795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32681 (p : Pattern) (guard : d6558 p = 1) : d2011 p ≤ (2 : Int) + d7252 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2011, d7252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32676 p hg
    simpa only [d2011, d7252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2011, d7252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32680 p hg
    simpa only [d2011, d7252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32682 (p : Pattern) (guard : d6558 p = 1) : d2012 p ≤ (2 : Int) + d7253 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2012, d7253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32681 p hg
    simpa only [d2012, d7253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2012, d7253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32680 p hg
    simpa only [d2012, d7253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32683 (p : Pattern) (guard : d6558 p = 1) : d2897 p ≤ (2 : Int) + d7254 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2897, d7254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32676 p hg
    simpa only [d2897, d7254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2897, d7254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32682 p hg
    simpa only [d2897, d7254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32684 (p : Pattern) (guard : d0 p = 1) : d4 p ≤ (2 : Int) + d6 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32685 (p : Pattern) (guard : d5842 p = 1) : d1693 p ≤ (2 : Int) + d6 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32684 p hg
    simpa only [d5842, d1693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15758 p hg
    simpa only [d5842, d1693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32686 (p : Pattern) (guard : d0 p = 1) : d34 p ≤ (2 : Int) + d6 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32687 (p : Pattern) (guard : d6558 p = 1) : d1694 p ≤ (2 : Int) + d6 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32685 p hg
    simpa only [d6558, d1694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32686 p hg
    simpa only [d6558, d1694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32688 (p : Pattern) (guard : d6558 p = 1) : d1695 p ≤ (2 : Int) + d7255 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1695, d7255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32676 p hg
    simpa only [d1695, d7255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1695, d7255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32687 p hg
    simpa only [d1695, d7255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32689 (p : Pattern) (guard : d6558 p = 1) : d1696 p ≤ (2 : Int) + d7256 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1696, d7256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32688 p hg
    simpa only [d1696, d7256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1696, d7256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32687 p hg
    simpa only [d1696, d7256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32690 (p : Pattern) (guard : d6558 p = 1) : d1697 p ≤ (2 : Int) + d7257 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1697, d7257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32689 p hg
    simpa only [d1697, d7257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1697, d7257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d1697, d7257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32691 (p : Pattern) (guard : d6558 p = 1) : d2898 p ≤ (2 : Int) + d7258 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2898, d7258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32683 p hg
    simpa only [d2898, d7258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2898, d7258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32690 p hg
    simpa only [d2898, d7258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32692 (p : Pattern) (guard : d6558 p = 1) : d2899 p ≤ (2 : Int) + d7259 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2899, d7259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32674 p hg
    simpa only [d2899, d7259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2899, d7259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32691 p hg
    simpa only [d2899, d7259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32693 (p : Pattern) (guard : d6558 p = 1) : d2900 p ≤ (2 : Int) + d7260 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2900, d7260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32674 p hg
    simpa only [d2900, d7260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2900, d7260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32692 p hg
    simpa only [d2900, d7260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32694 (p : Pattern) (guard : d5842 p = 1) : d9 p ≤ (2 : Int) + d9 p := by
  omega
theorem compare32695 (p : Pattern) (guard : d0 p = 1) : d23 p ≤ (2 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32696 (p : Pattern) (guard : d6558 p = 1) : d24 p ≤ (2 : Int) + d9 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32694 p hg
    simpa only [d6558, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32695 p hg
    simpa only [d6558, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32697 (p : Pattern) (guard : d0 p = 1) : d9 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32698 (p : Pattern) (guard : d5842 p = 1) : d23 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32697 p hg
    simpa only [d5842, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d5842, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32699 (p : Pattern) (guard : d6558 p = 1) : d356 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32698 p hg
    simpa only [d6558, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d6558, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32700 (p : Pattern) (guard : d6558 p = 1) : d1802 p ≤ (2 : Int) + d7261 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1802, d7261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32696 p hg
    simpa only [d1802, d7261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1802, d7261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32699 p hg
    simpa only [d1802, d7261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32701 (p : Pattern) (guard : d6558 p = 1) : d1803 p ≤ (2 : Int) + d7262 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1803, d7262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32700 p hg
    simpa only [d1803, d7262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1803, d7262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32699 p hg
    simpa only [d1803, d7262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32702 (p : Pattern) (guard : d6558 p = 1) : d2901 p ≤ (2 : Int) + d7263 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2901, d7263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32696 p hg
    simpa only [d2901, d7263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2901, d7263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32701 p hg
    simpa only [d2901, d7263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32703 (p : Pattern) (guard : d0 p = 1) : d9 p ≤ (2 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32704 (p : Pattern) (guard : d5842 p = 1) : d1701 p ≤ (2 : Int) + d11 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32703 p hg
    simpa only [d5842, d1701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15733 p hg
    simpa only [d5842, d1701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32705 (p : Pattern) (guard : d0 p = 1) : d39 p ≤ (2 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32706 (p : Pattern) (guard : d6558 p = 1) : d1702 p ≤ (2 : Int) + d11 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32704 p hg
    simpa only [d6558, d1702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32705 p hg
    simpa only [d6558, d1702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32707 (p : Pattern) (guard : d6558 p = 1) : d1703 p ≤ (2 : Int) + d7264 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1703, d7264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32696 p hg
    simpa only [d1703, d7264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1703, d7264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32706 p hg
    simpa only [d1703, d7264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32708 (p : Pattern) (guard : d6558 p = 1) : d1704 p ≤ (2 : Int) + d7265 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1704, d7265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32707 p hg
    simpa only [d1704, d7265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1704, d7265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32706 p hg
    simpa only [d1704, d7265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32709 (p : Pattern) (guard : d6558 p = 1) : d1705 p ≤ (2 : Int) + d7266 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1705, d7266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32708 p hg
    simpa only [d1705, d7266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1705, d7266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d1705, d7266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32710 (p : Pattern) (guard : d6558 p = 1) : d2902 p ≤ (2 : Int) + d7267 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2902, d7267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32702 p hg
    simpa only [d2902, d7267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2902, d7267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32709 p hg
    simpa only [d2902, d7267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32711 (p : Pattern) (guard : d6558 p = 1) : d2903 p ≤ (2 : Int) + d7268 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2903, d7268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32710 p hg
    simpa only [d2903, d7268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2903, d7268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d2903, d7268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32712 (p : Pattern) (guard : d6558 p = 1) : d2904 p ≤ (2 : Int) + d7269 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2904, d7269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32692 p hg
    simpa only [d2904, d7269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2904, d7269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32711 p hg
    simpa only [d2904, d7269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32713 (p : Pattern) (guard : d6558 p = 1) : d2905 p ≤ (2 : Int) + d7270 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2905, d7270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32693 p hg
    simpa only [d2905, d7270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2905, d7270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32712 p hg
    simpa only [d2905, d7270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32714 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (2 : Int) + d6 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32715 (p : Pattern) (guard : d5842 p = 1) : d1775 p ≤ (2 : Int) + d6 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32714 p hg
    simpa only [d5842, d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15758 p hg
    simpa only [d5842, d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32716 (p : Pattern) (guard : d6558 p = 1) : d1776 p ≤ (2 : Int) + d6 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32715 p hg
    simpa only [d6558, d1776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32686 p hg
    simpa only [d6558, d1776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32717 (p : Pattern) (guard : d6558 p = 1) : d1777 p ≤ (2 : Int) + d7271 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1777, d7271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32658 p hg
    simpa only [d1777, d7271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1777, d7271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32716 p hg
    simpa only [d1777, d7271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32718 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (2 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32719 (p : Pattern) (guard : d5842 p = 1) : d1785 p ≤ (2 : Int) + d9 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32718 p hg
    simpa only [d5842, d1785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4706 p hg
    simpa only [d5842, d1785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32720 (p : Pattern) (guard : d6558 p = 1) : d1786 p ≤ (2 : Int) + d9 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32719 p hg
    simpa only [d6558, d1786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32695 p hg
    simpa only [d6558, d1786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32721 (p : Pattern) (guard : d6558 p = 1) : d1787 p ≤ (2 : Int) + d7272 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1787, d7272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32662 p hg
    simpa only [d1787, d7272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1787, d7272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32720 p hg
    simpa only [d1787, d7272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32722 (p : Pattern) (guard : d6558 p = 1) : d1788 p ≤ (2 : Int) + d7273 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1788, d7273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32717 p hg
    simpa only [d1788, d7273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1788, d7273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32721 p hg
    simpa only [d1788, d7273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32723 (p : Pattern) (guard : d6558 p = 1) : d2906 p ≤ (2 : Int) + d7274 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2906, d7274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32658 p hg
    simpa only [d2906, d7274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2906, d7274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32722 p hg
    simpa only [d2906, d7274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32724 (p : Pattern) (guard : d5842 p = 1) : d2 p ≤ (2 : Int) + d2 p := by
  omega
theorem compare32725 (p : Pattern) (guard : d6558 p = 1) : d31 p ≤ (2 : Int) + d2 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32724 p hg
    simpa only [d6558, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32668 p hg
    simpa only [d6558, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32726 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32727 (p : Pattern) (guard : d5842 p = 1) : d1710 p ≤ (2 : Int) + d8 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32726 p hg
    simpa only [d5842, d1710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16154 p hg
    simpa only [d5842, d1710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32728 (p : Pattern) (guard : d6558 p = 1) : d1711 p ≤ (2 : Int) + d8 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32727 p hg
    simpa only [d6558, d1711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32679 p hg
    simpa only [d6558, d1711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32729 (p : Pattern) (guard : d6558 p = 1) : d1712 p ≤ (2 : Int) + d7275 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1712, d7275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32725 p hg
    simpa only [d1712, d7275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1712, d7275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32728 p hg
    simpa only [d1712, d7275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32730 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d6 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32731 (p : Pattern) (guard : d5842 p = 1) : d1713 p ≤ (2 : Int) + d6 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32730 p hg
    simpa only [d5842, d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15758 p hg
    simpa only [d5842, d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32732 (p : Pattern) (guard : d6558 p = 1) : d1714 p ≤ (2 : Int) + d6 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32731 p hg
    simpa only [d6558, d1714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32686 p hg
    simpa only [d6558, d1714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32733 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32734 (p : Pattern) (guard : d5842 p = 1) : d30 p ≤ (2 : Int) + d11 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32733 p hg
    simpa only [d5842, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4729 p hg
    simpa only [d5842, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32735 (p : Pattern) (guard : d6558 p = 1) : d1715 p ≤ (2 : Int) + d11 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32734 p hg
    simpa only [d6558, d1715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32705 p hg
    simpa only [d6558, d1715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32736 (p : Pattern) (guard : d6558 p = 1) : d1716 p ≤ (2 : Int) + d7276 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1716, d7276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32732 p hg
    simpa only [d1716, d7276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1716, d7276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32735 p hg
    simpa only [d1716, d7276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32737 (p : Pattern) (guard : d6558 p = 1) : d1717 p ≤ (2 : Int) + d7277 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1717, d7277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32729 p hg
    simpa only [d1717, d7277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1717, d7277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32736 p hg
    simpa only [d1717, d7277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32738 (p : Pattern) (guard : d6558 p = 1) : d1718 p ≤ (2 : Int) + d7278 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1718, d7278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32737 p hg
    simpa only [d1718, d7278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1718, d7278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d1718, d7278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32739 (p : Pattern) (guard : d6558 p = 1) : d2907 p ≤ (2 : Int) + d7279 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2907, d7279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32723 p hg
    simpa only [d2907, d7279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2907, d7279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32738 p hg
    simpa only [d2907, d7279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32740 (p : Pattern) (guard : d5842 p = 1) : d6 p ≤ (2 : Int) + d6 p := by
  omega
theorem compare32741 (p : Pattern) (guard : d6558 p = 1) : d35 p ≤ (2 : Int) + d6 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32740 p hg
    simpa only [d6558, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32686 p hg
    simpa only [d6558, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32742 (p : Pattern) (guard : d0 p = 1) : d6 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32743 (p : Pattern) (guard : d5842 p = 1) : d34 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32742 p hg
    simpa only [d5842, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d5842, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32744 (p : Pattern) (guard : d6558 p = 1) : d364 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32743 p hg
    simpa only [d6558, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d6558, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32745 (p : Pattern) (guard : d6558 p = 1) : d1720 p ≤ (2 : Int) + d7280 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1720, d7280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32741 p hg
    simpa only [d1720, d7280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1720, d7280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32744 p hg
    simpa only [d1720, d7280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32746 (p : Pattern) (guard : d0 p = 1) : d6 p ≤ (2 : Int) + d10 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32747 (p : Pattern) (guard : d5842 p = 1) : d1721 p ≤ (2 : Int) + d10 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32746 p hg
    simpa only [d5842, d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15723 p hg
    simpa only [d5842, d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32748 (p : Pattern) (guard : d0 p = 1) : d57 p ≤ (2 : Int) + d10 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32749 (p : Pattern) (guard : d6558 p = 1) : d1722 p ≤ (2 : Int) + d10 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32747 p hg
    simpa only [d6558, d1722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32748 p hg
    simpa only [d6558, d1722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32750 (p : Pattern) (guard : d6558 p = 1) : d1723 p ≤ (2 : Int) + d7281 p := by
  cases selected : p 225 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1723, d7281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32749 p hg
    simpa only [d1723, d7281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1723, d7281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32744 p hg
    simpa only [d1723, d7281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32751 (p : Pattern) (guard : d6558 p = 1) : d1724 p ≤ (2 : Int) + d7282 p := by
  cases selected : p 224 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1724, d7282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32745 p hg
    simpa only [d1724, d7282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1724, d7282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32750 p hg
    simpa only [d1724, d7282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32752 (p : Pattern) (guard : d6558 p = 1) : d1725 p ≤ (2 : Int) + d7283 p := by
  cases selected : p 204 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d1725, d7283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32751 p hg
    simpa only [d1725, d7283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d1725, d7283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32672 p hg
    simpa only [d1725, d7283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32753 (p : Pattern) (guard : d6558 p = 1) : d2908 p ≤ (2 : Int) + d7284 p := by
  cases selected : p 182 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2908, d7284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32723 p hg
    simpa only [d2908, d7284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2908, d7284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32752 p hg
    simpa only [d2908, d7284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32754 (p : Pattern) (guard : d6558 p = 1) : d2909 p ≤ (2 : Int) + d7285 p := by
  cases selected : p 163 with
  | false =>
    have hg : d6558 p = 1 := by simpa only [d2909, d7285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32739 p hg
    simpa only [d2909, d7285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6558 p = 1 := by simpa only [d2909, d7285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32753 p hg
    simpa only [d2909, d7285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32755 (p : Pattern) (guard : d5842 p = 1) : d11 p ≤ (2 : Int) + d11 p := by
  omega
theorem compare32756 (p : Pattern) (guard : d6558 p = 1) : d40 p ≤ (2 : Int) + d11 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32755 p hg
    simpa only [d6558, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32705 p hg
    simpa only [d6558, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32757 (p : Pattern) (guard : d0 p = 1) : d11 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare32758 (p : Pattern) (guard : d5842 p = 1) : d39 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5842, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32757 p hg
    simpa only [d5842, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5842, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d5842, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32759 (p : Pattern) (guard : d6558 p = 1) : d327 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5842 p = 1 := by simpa only [d6558, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32758 p hg
    simpa only [d6558, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6558, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d6558, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
