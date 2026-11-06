/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons103
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare14560 (p : Pattern) (guard : d0 p = 1) : d30 p ≤ (0 : Int) + d30 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14561 (p : Pattern) (guard : d5268 p = 1) : d31 p ≤ (0 : Int) + d30 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14559 p hg
    simpa only [d5268, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14560 p hg
    simpa only [d5268, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14562 (p : Pattern) (guard : d5269 p = 1) : d31 p ≤ (0 : Int) + d30 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14557 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14561 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14563 (p : Pattern) (guard : d5269 p = 1) : d32 p ≤ (0 : Int) + d5281 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d32, d5281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14562 p hg
    simpa only [d32, d5281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d32, d5281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d32, d5281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14564 (p : Pattern) (guard : d5269 p = 1) : d33 p ≤ (0 : Int) + d5282 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d33, d5282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14532 p hg
    simpa only [d33, d5282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d33, d5282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14563 p hg
    simpa only [d33, d5282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14565 (p : Pattern) (guard : d0 p = 1) : d35 p ≤ (0 : Int) + d34 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14566 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (0 : Int) + d6 p := by
  omega
theorem compare14567 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (0 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14566 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare955 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14568 (p : Pattern) (guard : d0 p = 1) : d34 p ≤ (0 : Int) + d34 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14569 (p : Pattern) (guard : d5268 p = 1) : d35 p ≤ (0 : Int) + d34 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14567 p hg
    simpa only [d5268, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14568 p hg
    simpa only [d5268, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14570 (p : Pattern) (guard : d5269 p = 1) : d35 p ≤ (0 : Int) + d34 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14565 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14569 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14571 (p : Pattern) (guard : d5269 p = 1) : d36 p ≤ (0 : Int) + d5283 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d36, d5283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14570 p hg
    simpa only [d36, d5283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d36, d5283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d36, d5283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14572 (p : Pattern) (guard : d5269 p = 1) : d37 p ≤ (0 : Int) + d5284 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d37, d5284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14532 p hg
    simpa only [d37, d5284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d37, d5284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14571 p hg
    simpa only [d37, d5284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14573 (p : Pattern) (guard : d5269 p = 1) : d38 p ≤ (0 : Int) + d5285 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d38, d5285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14564 p hg
    simpa only [d38, d5285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d38, d5285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14572 p hg
    simpa only [d38, d5285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14574 (p : Pattern) (guard : d0 p = 1) : d40 p ≤ (0 : Int) + d39 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14575 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (0 : Int) + d11 p := by
  omega
theorem compare14576 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14575 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare709 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14577 (p : Pattern) (guard : d0 p = 1) : d39 p ≤ (0 : Int) + d39 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14578 (p : Pattern) (guard : d5268 p = 1) : d40 p ≤ (0 : Int) + d39 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14576 p hg
    simpa only [d5268, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14577 p hg
    simpa only [d5268, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14579 (p : Pattern) (guard : d5269 p = 1) : d40 p ≤ (0 : Int) + d39 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14574 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14578 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14580 (p : Pattern) (guard : d5269 p = 1) : d41 p ≤ (0 : Int) + d5286 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d41, d5286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14579 p hg
    simpa only [d41, d5286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d41, d5286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d41, d5286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14581 (p : Pattern) (guard : d5269 p = 1) : d42 p ≤ (0 : Int) + d5287 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d42, d5287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14532 p hg
    simpa only [d42, d5287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d42, d5287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14580 p hg
    simpa only [d42, d5287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14582 (p : Pattern) (guard : d5269 p = 1) : d43 p ≤ (0 : Int) + d5288 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d43, d5288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14541 p hg
    simpa only [d43, d5288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d43, d5288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d43, d5288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14583 (p : Pattern) (guard : d5269 p = 1) : d44 p ≤ (0 : Int) + d5289 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d44, d5289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14581 p hg
    simpa only [d44, d5289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d44, d5289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14582 p hg
    simpa only [d44, d5289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14584 (p : Pattern) (guard : d5269 p = 1) : d45 p ≤ (0 : Int) + d5290 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d45, d5290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14573 p hg
    simpa only [d45, d5290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d45, d5290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14583 p hg
    simpa only [d45, d5290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14585 (p : Pattern) (guard : d5269 p = 1) : d46 p ≤ (0 : Int) + d5291 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d46, d5291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14532 p hg
    simpa only [d46, d5291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d46, d5291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d46, d5291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14586 (p : Pattern) (guard : d5269 p = 1) : d47 p ≤ (0 : Int) + d5292 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d47, d5292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14585 p hg
    simpa only [d47, d5292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d47, d5292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14582 p hg
    simpa only [d47, d5292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14587 (p : Pattern) (guard : d5269 p = 1) : d48 p ≤ (0 : Int) + d5293 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d48, d5293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14551 p hg
    simpa only [d48, d5293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d48, d5293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d48, d5293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14588 (p : Pattern) (guard : d5269 p = 1) : d49 p ≤ (0 : Int) + d5294 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d49, d5294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14587 p hg
    simpa only [d49, d5294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d49, d5294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d49, d5294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14589 (p : Pattern) (guard : d5269 p = 1) : d50 p ≤ (0 : Int) + d5295 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d50, d5295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14586 p hg
    simpa only [d50, d5295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d50, d5295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14588 p hg
    simpa only [d50, d5295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14590 (p : Pattern) (guard : d5269 p = 1) : d51 p ≤ (0 : Int) + d5296 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d51, d5296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14584 p hg
    simpa only [d51, d5296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d51, d5296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14589 p hg
    simpa only [d51, d5296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14591 (p : Pattern) (guard : d5269 p = 1) : d52 p ≤ (0 : Int) + d5297 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d52, d5297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14556 p hg
    simpa only [d52, d5297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d52, d5297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14590 p hg
    simpa only [d52, d5297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14592 (p : Pattern) (guard : d5269 p = 1) : d53 p ≤ (0 : Int) + d5298 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d53, d5298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14562 p hg
    simpa only [d53, d5298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d53, d5298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14563 p hg
    simpa only [d53, d5298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14593 (p : Pattern) (guard : d5269 p = 1) : d54 p ≤ (0 : Int) + d5299 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d54, d5299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14535 p hg
    simpa only [d54, d5299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d54, d5299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14592 p hg
    simpa only [d54, d5299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14594 (p : Pattern) (guard : d5269 p = 1) : d55 p ≤ (0 : Int) + d5300 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d55, d5300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14543 p hg
    simpa only [d55, d5300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d55, d5300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14553 p hg
    simpa only [d55, d5300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14595 (p : Pattern) (guard : d5269 p = 1) : d56 p ≤ (0 : Int) + d5301 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d56, d5301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14593 p hg
    simpa only [d56, d5301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d56, d5301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14594 p hg
    simpa only [d56, d5301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14596 (p : Pattern) (guard : d0 p = 1) : d58 p ≤ (0 : Int) + d57 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14597 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (0 : Int) + d10 p := by
  omega
theorem compare14598 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14597 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare813 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14599 (p : Pattern) (guard : d0 p = 1) : d57 p ≤ (0 : Int) + d57 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14600 (p : Pattern) (guard : d5268 p = 1) : d58 p ≤ (0 : Int) + d57 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14598 p hg
    simpa only [d5268, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14599 p hg
    simpa only [d5268, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14601 (p : Pattern) (guard : d5269 p = 1) : d58 p ≤ (0 : Int) + d57 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14596 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14600 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14602 (p : Pattern) (guard : d5269 p = 1) : d59 p ≤ (0 : Int) + d5302 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d59, d5302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14601 p hg
    simpa only [d59, d5302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d59, d5302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d59, d5302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14603 (p : Pattern) (guard : d5269 p = 1) : d60 p ≤ (0 : Int) + d5303 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d60, d5303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14601 p hg
    simpa only [d60, d5303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d60, d5303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14602 p hg
    simpa only [d60, d5303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14604 (p : Pattern) (guard : d5269 p = 1) : d61 p ≤ (0 : Int) + d5304 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d61, d5304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14543 p hg
    simpa only [d61, d5304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d61, d5304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14603 p hg
    simpa only [d61, d5304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14605 (p : Pattern) (guard : d5269 p = 1) : d62 p ≤ (0 : Int) + d5305 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d62, d5305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14579 p hg
    simpa only [d62, d5305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d62, d5305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14580 p hg
    simpa only [d62, d5305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14606 (p : Pattern) (guard : d5269 p = 1) : d63 p ≤ (0 : Int) + d5306 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d63, d5306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14605 p hg
    simpa only [d63, d5306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d63, d5306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d63, d5306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14607 (p : Pattern) (guard : d5269 p = 1) : d64 p ≤ (0 : Int) + d5307 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d64, d5307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14604 p hg
    simpa only [d64, d5307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d64, d5307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14606 p hg
    simpa only [d64, d5307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14608 (p : Pattern) (guard : d5269 p = 1) : d65 p ≤ (0 : Int) + d5308 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d65, d5308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14595 p hg
    simpa only [d65, d5308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d65, d5308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14607 p hg
    simpa only [d65, d5308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14609 (p : Pattern) (guard : d5269 p = 1) : d66 p ≤ (0 : Int) + d5309 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d66, d5309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14562 p hg
    simpa only [d66, d5309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d66, d5309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d66, d5309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14610 (p : Pattern) (guard : d5269 p = 1) : d67 p ≤ (0 : Int) + d5310 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d67, d5310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14572 p hg
    simpa only [d67, d5310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d67, d5310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14609 p hg
    simpa only [d67, d5310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14611 (p : Pattern) (guard : d5269 p = 1) : d68 p ≤ (0 : Int) + d5311 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d68, d5311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14582 p hg
    simpa only [d68, d5311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d68, d5311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14587 p hg
    simpa only [d68, d5311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14612 (p : Pattern) (guard : d5269 p = 1) : d69 p ≤ (0 : Int) + d5312 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d69, d5312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14610 p hg
    simpa only [d69, d5312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d69, d5312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14611 p hg
    simpa only [d69, d5312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14613 (p : Pattern) (guard : d5269 p = 1) : d70 p ≤ (0 : Int) + d5313 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d70, d5313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14601 p hg
    simpa only [d70, d5313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d70, d5313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d70, d5313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14614 (p : Pattern) (guard : d5269 p = 1) : d71 p ≤ (0 : Int) + d5314 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d71, d5314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14582 p hg
    simpa only [d71, d5314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d71, d5314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14613 p hg
    simpa only [d71, d5314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14615 (p : Pattern) (guard : d5269 p = 1) : d72 p ≤ (0 : Int) + d5315 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d72, d5315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14579 p hg
    simpa only [d72, d5315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d72, d5315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d72, d5315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14616 (p : Pattern) (guard : d5269 p = 1) : d73 p ≤ (0 : Int) + d5316 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d73, d5316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14615 p hg
    simpa only [d73, d5316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d73, d5316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d73, d5316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14617 (p : Pattern) (guard : d5269 p = 1) : d74 p ≤ (0 : Int) + d5317 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d74, d5317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14614 p hg
    simpa only [d74, d5317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d74, d5317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14616 p hg
    simpa only [d74, d5317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14618 (p : Pattern) (guard : d5269 p = 1) : d75 p ≤ (0 : Int) + d5318 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d75, d5318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14612 p hg
    simpa only [d75, d5318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d75, d5318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14617 p hg
    simpa only [d75, d5318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14619 (p : Pattern) (guard : d5269 p = 1) : d76 p ≤ (0 : Int) + d5319 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d76, d5319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14608 p hg
    simpa only [d76, d5319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d76, d5319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14618 p hg
    simpa only [d76, d5319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14620 (p : Pattern) (guard : d5269 p = 1) : d77 p ≤ (0 : Int) + d5320 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d77, d5320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14591 p hg
    simpa only [d77, d5320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d77, d5320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14619 p hg
    simpa only [d77, d5320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14621 (p : Pattern) (guard : d5269 p = 1) : d78 p ≤ (0 : Int) + d5321 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d78, d5321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14570 p hg
    simpa only [d78, d5321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d78, d5321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14571 p hg
    simpa only [d78, d5321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14622 (p : Pattern) (guard : d5269 p = 1) : d79 p ≤ (0 : Int) + d5322 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d79, d5322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14592 p hg
    simpa only [d79, d5322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d79, d5322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14621 p hg
    simpa only [d79, d5322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14623 (p : Pattern) (guard : d5269 p = 1) : d80 p ≤ (0 : Int) + d5323 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d80, d5323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14622 p hg
    simpa only [d80, d5323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d80, d5323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14606 p hg
    simpa only [d80, d5323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14624 (p : Pattern) (guard : d5269 p = 1) : d81 p ≤ (0 : Int) + d5324 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d81, d5324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14623 p hg
    simpa only [d81, d5324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d81, d5324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d81, d5324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14625 (p : Pattern) (guard : d5269 p = 1) : d82 p ≤ (0 : Int) + d5325 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d82, d5325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14556 p hg
    simpa only [d82, d5325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d82, d5325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14624 p hg
    simpa only [d82, d5325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14626 (p : Pattern) (guard : d5269 p = 1) : d83 p ≤ (0 : Int) + d5326 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d83, d5326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14621 p hg
    simpa only [d83, d5326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d83, d5326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d83, d5326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14627 (p : Pattern) (guard : d5269 p = 1) : d84 p ≤ (0 : Int) + d5327 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d84, d5327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14626 p hg
    simpa only [d84, d5327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d84, d5327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d84, d5327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14628 (p : Pattern) (guard : d5269 p = 1) : d85 p ≤ (0 : Int) + d5328 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d85, d5328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14627 p hg
    simpa only [d85, d5328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d85, d5328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d85, d5328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14629 (p : Pattern) (guard : d5269 p = 1) : d86 p ≤ (0 : Int) + d5329 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d86, d5329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14608 p hg
    simpa only [d86, d5329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d86, d5329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14628 p hg
    simpa only [d86, d5329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14630 (p : Pattern) (guard : d5269 p = 1) : d87 p ≤ (0 : Int) + d5330 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d87, d5330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14625 p hg
    simpa only [d87, d5330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d87, d5330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14629 p hg
    simpa only [d87, d5330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14631 (p : Pattern) (guard : d5269 p = 1) : d88 p ≤ (0 : Int) + d5331 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d88, d5331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14620 p hg
    simpa only [d88, d5331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d88, d5331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14630 p hg
    simpa only [d88, d5331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14632 (p : Pattern) (guard : d5269 p = 1) : d89 p ≤ (0 : Int) + d5332 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d89, d5332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14553 p hg
    simpa only [d89, d5332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d89, d5332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14605 p hg
    simpa only [d89, d5332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14633 (p : Pattern) (guard : d5269 p = 1) : d90 p ≤ (0 : Int) + d5333 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d90, d5333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14632 p hg
    simpa only [d90, d5333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d90, d5333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14606 p hg
    simpa only [d90, d5333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14634 (p : Pattern) (guard : d5269 p = 1) : d91 p ≤ (0 : Int) + d5334 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d91, d5334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14606 p hg
    simpa only [d91, d5334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d91, d5334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d91, d5334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14635 (p : Pattern) (guard : d5269 p = 1) : d92 p ≤ (0 : Int) + d5335 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d92, d5335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14633 p hg
    simpa only [d92, d5335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d92, d5335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14634 p hg
    simpa only [d92, d5335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14636 (p : Pattern) (guard : d5269 p = 1) : d93 p ≤ (0 : Int) + d5336 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d93, d5336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14634 p hg
    simpa only [d93, d5336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d93, d5336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d93, d5336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14637 (p : Pattern) (guard : d5269 p = 1) : d94 p ≤ (0 : Int) + d5337 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d94, d5337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14635 p hg
    simpa only [d94, d5337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d94, d5337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14636 p hg
    simpa only [d94, d5337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14638 (p : Pattern) (guard : d5269 p = 1) : d95 p ≤ (0 : Int) + d5338 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d95, d5338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14636 p hg
    simpa only [d95, d5338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d95, d5338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d95, d5338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14639 (p : Pattern) (guard : d5269 p = 1) : d96 p ≤ (0 : Int) + d5339 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d96, d5339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14637 p hg
    simpa only [d96, d5339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d96, d5339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14638 p hg
    simpa only [d96, d5339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14640 (p : Pattern) (guard : d5269 p = 1) : d97 p ≤ (0 : Int) + d5340 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d97, d5340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14630 p hg
    simpa only [d97, d5340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d97, d5340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14639 p hg
    simpa only [d97, d5340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14641 (p : Pattern) (guard : d5269 p = 1) : d98 p ≤ (0 : Int) + d5341 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d98, d5341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14631 p hg
    simpa only [d98, d5341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d98, d5341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14640 p hg
    simpa only [d98, d5341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14642 (p : Pattern) (guard : d5269 p = 1) : d99 p ≤ (0 : Int) + d5342 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d99, d5342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14630 p hg
    simpa only [d99, d5342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d99, d5342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d99, d5342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14643 (p : Pattern) (guard : d5269 p = 1) : d100 p ≤ (0 : Int) + d5343 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d100, d5343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14631 p hg
    simpa only [d100, d5343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d100, d5343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14642 p hg
    simpa only [d100, d5343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14644 (p : Pattern) (guard : d5269 p = 1) : d101 p ≤ (0 : Int) + d5344 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d101, d5344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14641 p hg
    simpa only [d101, d5344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d101, d5344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14643 p hg
    simpa only [d101, d5344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14645 (p : Pattern) (guard : d0 p = 1) : d103 p ≤ (0 : Int) + d102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14646 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d1 p := by
  omega
theorem compare14647 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d102 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1561 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14648 (p : Pattern) (guard : d0 p = 1) : d102 p ≤ (0 : Int) + d102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14649 (p : Pattern) (guard : d5268 p = 1) : d103 p ≤ (0 : Int) + d102 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14647 p hg
    simpa only [d5268, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14648 p hg
    simpa only [d5268, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14650 (p : Pattern) (guard : d5269 p = 1) : d103 p ≤ (0 : Int) + d102 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14645 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14649 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14651 (p : Pattern) (guard : d5269 p = 1) : d104 p ≤ (0 : Int) + d5345 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d104, d5345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14650 p hg
    simpa only [d104, d5345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d104, d5345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d104, d5345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14652 (p : Pattern) (guard : d5269 p = 1) : d105 p ≤ (0 : Int) + d5346 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d105, d5346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14650 p hg
    simpa only [d105, d5346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d105, d5346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14651 p hg
    simpa only [d105, d5346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14653 (p : Pattern) (guard : d0 p = 1) : d107 p ≤ (0 : Int) + d106 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14654 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (0 : Int) + d5 p := by
  omega
theorem compare14655 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (0 : Int) + d106 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14654 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1319 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14656 (p : Pattern) (guard : d0 p = 1) : d106 p ≤ (0 : Int) + d106 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14657 (p : Pattern) (guard : d5268 p = 1) : d107 p ≤ (0 : Int) + d106 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14655 p hg
    simpa only [d5268, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14656 p hg
    simpa only [d5268, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14658 (p : Pattern) (guard : d5269 p = 1) : d107 p ≤ (0 : Int) + d106 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14653 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14657 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14659 (p : Pattern) (guard : d5269 p = 1) : d108 p ≤ (0 : Int) + d5347 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d108, d5347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14658 p hg
    simpa only [d108, d5347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d108, d5347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d108, d5347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14660 (p : Pattern) (guard : d5269 p = 1) : d109 p ≤ (0 : Int) + d5348 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d109, d5348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14658 p hg
    simpa only [d109, d5348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d109, d5348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14659 p hg
    simpa only [d109, d5348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14661 (p : Pattern) (guard : d5269 p = 1) : d110 p ≤ (0 : Int) + d5349 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d110, d5349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14652 p hg
    simpa only [d110, d5349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d110, d5349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14660 p hg
    simpa only [d110, d5349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14662 (p : Pattern) (guard : d5269 p = 1) : d111 p ≤ (0 : Int) + d5350 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d111, d5350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14652 p hg
    simpa only [d111, d5350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d111, d5350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14661 p hg
    simpa only [d111, d5350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14663 (p : Pattern) (guard : d5269 p = 1) : d112 p ≤ (0 : Int) + d5351 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d112, d5351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14603 p hg
    simpa only [d112, d5351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d112, d5351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d112, d5351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14664 (p : Pattern) (guard : d5269 p = 1) : d113 p ≤ (0 : Int) + d5352 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d113, d5352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14661 p hg
    simpa only [d113, d5352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d113, d5352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14663 p hg
    simpa only [d113, d5352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14665 (p : Pattern) (guard : d5269 p = 1) : d114 p ≤ (0 : Int) + d5353 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d114, d5353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14662 p hg
    simpa only [d114, d5353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d114, d5353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14664 p hg
    simpa only [d114, d5353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14666 (p : Pattern) (guard : d0 p = 1) : d116 p ≤ (0 : Int) + d115 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14667 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (0 : Int) + d3 p := by
  omega
theorem compare14668 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (0 : Int) + d115 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14667 p hg
    simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1571 p hg
    simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14669 (p : Pattern) (guard : d0 p = 1) : d115 p ≤ (0 : Int) + d115 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14670 (p : Pattern) (guard : d5268 p = 1) : d116 p ≤ (0 : Int) + d115 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14668 p hg
    simpa only [d5268, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14669 p hg
    simpa only [d5268, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14671 (p : Pattern) (guard : d5269 p = 1) : d116 p ≤ (0 : Int) + d115 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14666 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14670 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14672 (p : Pattern) (guard : d5269 p = 1) : d117 p ≤ (0 : Int) + d5354 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d117, d5354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14671 p hg
    simpa only [d117, d5354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d117, d5354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d117, d5354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14673 (p : Pattern) (guard : d5269 p = 1) : d118 p ≤ (0 : Int) + d5355 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d118, d5355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14650 p hg
    simpa only [d118, d5355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d118, d5355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14672 p hg
    simpa only [d118, d5355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14674 (p : Pattern) (guard : d0 p = 1) : d120 p ≤ (0 : Int) + d119 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14675 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (0 : Int) + d7 p := by
  omega
theorem compare14676 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (0 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14675 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1280 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14677 (p : Pattern) (guard : d0 p = 1) : d119 p ≤ (0 : Int) + d119 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14678 (p : Pattern) (guard : d5268 p = 1) : d120 p ≤ (0 : Int) + d119 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14676 p hg
    simpa only [d5268, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14677 p hg
    simpa only [d5268, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14679 (p : Pattern) (guard : d5269 p = 1) : d120 p ≤ (0 : Int) + d119 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14674 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14678 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14680 (p : Pattern) (guard : d5269 p = 1) : d121 p ≤ (0 : Int) + d5356 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d121, d5356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14679 p hg
    simpa only [d121, d5356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d121, d5356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d121, d5356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14681 (p : Pattern) (guard : d5269 p = 1) : d122 p ≤ (0 : Int) + d5357 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d122, d5357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14650 p hg
    simpa only [d122, d5357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d122, d5357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14680 p hg
    simpa only [d122, d5357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14682 (p : Pattern) (guard : d5269 p = 1) : d123 p ≤ (0 : Int) + d5358 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d123, d5358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14673 p hg
    simpa only [d123, d5358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d123, d5358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14681 p hg
    simpa only [d123, d5358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14683 (p : Pattern) (guard : d5269 p = 1) : d124 p ≤ (0 : Int) + d5359 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d124, d5359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14650 p hg
    simpa only [d124, d5359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d124, d5359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d124, d5359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14684 (p : Pattern) (guard : d5269 p = 1) : d125 p ≤ (0 : Int) + d5360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d125, d5360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14658 p hg
    simpa only [d125, d5360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d125, d5360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d125, d5360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14685 (p : Pattern) (guard : d5269 p = 1) : d126 p ≤ (0 : Int) + d5361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d126, d5361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14683 p hg
    simpa only [d126, d5361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d126, d5361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14684 p hg
    simpa only [d126, d5361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14686 (p : Pattern) (guard : d5269 p = 1) : d127 p ≤ (0 : Int) + d5362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d127, d5362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14682 p hg
    simpa only [d127, d5362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d127, d5362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14685 p hg
    simpa only [d127, d5362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14687 (p : Pattern) (guard : d5269 p = 1) : d128 p ≤ (0 : Int) + d5363 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d128, d5363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14613 p hg
    simpa only [d128, d5363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d128, d5363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d128, d5363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14688 (p : Pattern) (guard : d5269 p = 1) : d129 p ≤ (0 : Int) + d5364 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d129, d5364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14685 p hg
    simpa only [d129, d5364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d129, d5364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14687 p hg
    simpa only [d129, d5364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14689 (p : Pattern) (guard : d5269 p = 1) : d130 p ≤ (0 : Int) + d5365 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d130, d5365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14686 p hg
    simpa only [d130, d5365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d130, d5365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14688 p hg
    simpa only [d130, d5365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14690 (p : Pattern) (guard : d5269 p = 1) : d131 p ≤ (0 : Int) + d5366 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d131, d5366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14665 p hg
    simpa only [d131, d5366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d131, d5366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14689 p hg
    simpa only [d131, d5366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14691 (p : Pattern) (guard : d5269 p = 1) : d132 p ≤ (0 : Int) + d5367 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d132, d5367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14671 p hg
    simpa only [d132, d5367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d132, d5367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14672 p hg
    simpa only [d132, d5367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14692 (p : Pattern) (guard : d5269 p = 1) : d133 p ≤ (0 : Int) + d5368 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d133, d5368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14652 p hg
    simpa only [d133, d5368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d133, d5368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14691 p hg
    simpa only [d133, d5368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14693 (p : Pattern) (guard : d5269 p = 1) : d134 p ≤ (0 : Int) + d5369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d134, d5369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14660 p hg
    simpa only [d134, d5369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d134, d5369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14603 p hg
    simpa only [d134, d5369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14694 (p : Pattern) (guard : d5269 p = 1) : d135 p ≤ (0 : Int) + d5370 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d135, d5370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14692 p hg
    simpa only [d135, d5370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d135, d5370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14693 p hg
    simpa only [d135, d5370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14695 (p : Pattern) (guard : d5269 p = 1) : d136 p ≤ (0 : Int) + d5371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d136, d5371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14660 p hg
    simpa only [d136, d5371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d136, d5371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14605 p hg
    simpa only [d136, d5371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14696 (p : Pattern) (guard : d5269 p = 1) : d137 p ≤ (0 : Int) + d5372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d137, d5372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14695 p hg
    simpa only [d137, d5372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d137, d5372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d137, d5372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14697 (p : Pattern) (guard : d5269 p = 1) : d138 p ≤ (0 : Int) + d5373 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d138, d5373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14694 p hg
    simpa only [d138, d5373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d138, d5373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14696 p hg
    simpa only [d138, d5373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14698 (p : Pattern) (guard : d5269 p = 1) : d139 p ≤ (0 : Int) + d5374 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d139, d5374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14671 p hg
    simpa only [d139, d5374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d139, d5374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d139, d5374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14699 (p : Pattern) (guard : d5269 p = 1) : d140 p ≤ (0 : Int) + d5375 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d140, d5375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14681 p hg
    simpa only [d140, d5375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d140, d5375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14698 p hg
    simpa only [d140, d5375, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
