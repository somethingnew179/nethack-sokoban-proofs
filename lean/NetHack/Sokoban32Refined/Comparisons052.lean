/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons051
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare7280 (p : Pattern) (guard : d1167 p = 1) : d7 p ≤ (0 : Int) + d31 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d7, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare659 p hg
    simpa only [d1167, d7, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d7, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6268 p hg
    simpa only [d1167, d7, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7281 (p : Pattern) (guard : d1171 p = 1) : d7 p ≤ (0 : Int) + d551 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7280 p hg
    simpa only [d1171, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2350 p hg
    simpa only [d1171, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7282 (p : Pattern) (guard : d1171 p = 1) : d653 p ≤ (0 : Int) + d552 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d653, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7281 p hg
    simpa only [d653, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d653, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7275 p hg
    simpa only [d653, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7283 (p : Pattern) (guard : d1171 p = 1) : d654 p ≤ (0 : Int) + d553 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d654, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7281 p hg
    simpa only [d654, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d654, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7282 p hg
    simpa only [d654, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7284 (p : Pattern) (guard : d1171 p = 1) : d654 p ≤ (0 : Int) + d554 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7269 p hg
    simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7283 p hg
    simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7285 (p : Pattern) (guard : d1171 p = 1) : d654 p ≤ (0 : Int) + d555 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7284 p hg
    simpa only [d555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7278 p hg
    simpa only [d555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7286 (p : Pattern) (guard : d1171 p = 1) : d654 p ≤ (0 : Int) + d556 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7279 p hg
    simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7285 p hg
    simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7287 (p : Pattern) (guard : d1171 p = 1) : d653 p ≤ (0 : Int) + d557 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7268 p hg
    simpa only [d557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7276 p hg
    simpa only [d557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7288 (p : Pattern) (guard : d1171 p = 1) : d653 p ≤ (0 : Int) + d558 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7268 p hg
    simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7287 p hg
    simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7289 (p : Pattern) (guard : d1171 p = 1) : d653 p ≤ (0 : Int) + d559 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7268 p hg
    simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7282 p hg
    simpa only [d559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7290 (p : Pattern) (guard : d1171 p = 1) : d653 p ≤ (0 : Int) + d560 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7289 p hg
    simpa only [d560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7287 p hg
    simpa only [d560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7291 (p : Pattern) (guard : d1171 p = 1) : d653 p ≤ (0 : Int) + d561 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7288 p hg
    simpa only [d561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7290 p hg
    simpa only [d561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7292 (p : Pattern) (guard : d1171 p = 1) : d655 p ≤ (0 : Int) + d562 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d655, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7266 p hg
    simpa only [d655, d562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d655, d562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d655, d562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7293 (p : Pattern) (guard : d1171 p = 1) : d656 p ≤ (0 : Int) + d563 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d656, d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7268 p hg
    simpa only [d656, d563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d656, d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7292 p hg
    simpa only [d656, d563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7294 (p : Pattern) (guard : d1171 p = 1) : d655 p ≤ (0 : Int) + d564 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d655, d564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7273 p hg
    simpa only [d655, d564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d655, d564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d655, d564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7295 (p : Pattern) (guard : d1171 p = 1) : d656 p ≤ (0 : Int) + d565 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d656, d565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7276 p hg
    simpa only [d656, d565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d656, d565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7294 p hg
    simpa only [d656, d565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7296 (p : Pattern) (guard : d1171 p = 1) : d656 p ≤ (0 : Int) + d566 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7293 p hg
    simpa only [d566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7295 p hg
    simpa only [d566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7297 (p : Pattern) (guard : d1171 p = 1) : d656 p ≤ (0 : Int) + d567 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7293 p hg
    simpa only [d567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7296 p hg
    simpa only [d567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7298 (p : Pattern) (guard : d1171 p = 1) : d655 p ≤ (0 : Int) + d568 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d655, d568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7281 p hg
    simpa only [d655, d568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d655, d568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d655, d568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7299 (p : Pattern) (guard : d1171 p = 1) : d656 p ≤ (0 : Int) + d569 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d656, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7282 p hg
    simpa only [d656, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d656, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7298 p hg
    simpa only [d656, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7300 (p : Pattern) (guard : d1171 p = 1) : d656 p ≤ (0 : Int) + d570 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7293 p hg
    simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7299 p hg
    simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7301 (p : Pattern) (guard : d1171 p = 1) : d656 p ≤ (0 : Int) + d571 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7300 p hg
    simpa only [d571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7296 p hg
    simpa only [d571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7302 (p : Pattern) (guard : d1171 p = 1) : d656 p ≤ (0 : Int) + d572 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7297 p hg
    simpa only [d572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7301 p hg
    simpa only [d572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7303 (p : Pattern) (guard : d1171 p = 1) : d657 p ≤ (0 : Int) + d573 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d657, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7291 p hg
    simpa only [d657, d573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d657, d573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7302 p hg
    simpa only [d657, d573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7304 (p : Pattern) (guard : d1171 p = 1) : d658 p ≤ (0 : Int) + d574 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d658, d574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7286 p hg
    simpa only [d658, d574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d658, d574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7303 p hg
    simpa only [d658, d574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7305 (p : Pattern) (guard : d1171 p = 1) : d654 p ≤ (0 : Int) + d575 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7269 p hg
    simpa only [d575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7277 p hg
    simpa only [d575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7306 (p : Pattern) (guard : d1171 p = 1) : d659 p ≤ (0 : Int) + d576 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d659, d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7267 p hg
    simpa only [d659, d576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d659, d576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d659, d576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7307 (p : Pattern) (guard : d1171 p = 1) : d660 p ≤ (0 : Int) + d577 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d660, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7267 p hg
    simpa only [d660, d577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d660, d577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7306 p hg
    simpa only [d660, d577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7308 (p : Pattern) (guard : d1171 p = 1) : d659 p ≤ (0 : Int) + d578 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d659, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7275 p hg
    simpa only [d659, d578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d659, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d659, d578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7309 (p : Pattern) (guard : d1171 p = 1) : d660 p ≤ (0 : Int) + d579 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d660, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7275 p hg
    simpa only [d660, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d660, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7308 p hg
    simpa only [d660, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7310 (p : Pattern) (guard : d1171 p = 1) : d660 p ≤ (0 : Int) + d580 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7307 p hg
    simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7309 p hg
    simpa only [d580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7311 (p : Pattern) (guard : d1171 p = 1) : d661 p ≤ (0 : Int) + d581 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d661, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7305 p hg
    simpa only [d661, d581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d661, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7310 p hg
    simpa only [d661, d581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7312 (p : Pattern) (guard : d1171 p = 1) : d662 p ≤ (0 : Int) + d582 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d662, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7279 p hg
    simpa only [d662, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d662, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7311 p hg
    simpa only [d662, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7313 (p : Pattern) (guard : d1171 p = 1) : d7 p ≤ (0 : Int) + d583 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7265 p hg
    simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7266 p hg
    simpa only [d583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7314 (p : Pattern) (guard : d1171 p = 1) : d654 p ≤ (0 : Int) + d584 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d654, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7313 p hg
    simpa only [d654, d584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d654, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7268 p hg
    simpa only [d654, d584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7315 (p : Pattern) (guard : d1171 p = 1) : d654 p ≤ (0 : Int) + d585 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7314 p hg
    simpa only [d585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7277 p hg
    simpa only [d585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7316 (p : Pattern) (guard : d1171 p = 1) : d659 p ≤ (0 : Int) + d586 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7306 p hg
    simpa only [d586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7308 p hg
    simpa only [d586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7317 (p : Pattern) (guard : d1171 p = 1) : d663 p ≤ (0 : Int) + d587 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d663, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7315 p hg
    simpa only [d663, d587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d663, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7316 p hg
    simpa only [d663, d587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7318 (p : Pattern) (guard : d1171 p = 1) : d664 p ≤ (0 : Int) + d588 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d664, d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7279 p hg
    simpa only [d664, d588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d664, d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7317 p hg
    simpa only [d664, d588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7319 (p : Pattern) (guard : d1171 p = 1) : d665 p ≤ (0 : Int) + d589 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d665, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7312 p hg
    simpa only [d665, d589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d665, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7318 p hg
    simpa only [d665, d589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7320 (p : Pattern) (guard : d1171 p = 1) : d666 p ≤ (0 : Int) + d590 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d666, d590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7287 p hg
    simpa only [d666, d590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d666, d590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7316 p hg
    simpa only [d666, d590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7321 (p : Pattern) (guard : d1171 p = 1) : d667 p ≤ (0 : Int) + d591 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d667, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7288 p hg
    simpa only [d667, d591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d667, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7320 p hg
    simpa only [d667, d591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7322 (p : Pattern) (guard : d1171 p = 1) : d668 p ≤ (0 : Int) + d592 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d668, d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7296 p hg
    simpa only [d668, d592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d668, d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7316 p hg
    simpa only [d668, d592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7323 (p : Pattern) (guard : d1171 p = 1) : d669 p ≤ (0 : Int) + d593 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d669, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7297 p hg
    simpa only [d669, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d669, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7322 p hg
    simpa only [d669, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7324 (p : Pattern) (guard : d1171 p = 1) : d670 p ≤ (0 : Int) + d594 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d670, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7321 p hg
    simpa only [d670, d594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d670, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7323 p hg
    simpa only [d670, d594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7325 (p : Pattern) (guard : d1171 p = 1) : d671 p ≤ (0 : Int) + d595 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d671, d595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7319 p hg
    simpa only [d671, d595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d671, d595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7324 p hg
    simpa only [d671, d595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7326 (p : Pattern) (guard : d1171 p = 1) : d672 p ≤ (0 : Int) + d596 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d672, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7304 p hg
    simpa only [d672, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d672, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7325 p hg
    simpa only [d672, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7327 (p : Pattern) (guard : d1171 p = 1) : d673 p ≤ (0 : Int) + d597 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d673, d597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7265 p hg
    simpa only [d673, d597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d673, d597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7292 p hg
    simpa only [d673, d597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7328 (p : Pattern) (guard : d1171 p = 1) : d673 p ≤ (0 : Int) + d598 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d673, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7266 p hg
    simpa only [d673, d598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d673, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7292 p hg
    simpa only [d673, d598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7329 (p : Pattern) (guard : d1171 p = 1) : d673 p ≤ (0 : Int) + d599 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7327 p hg
    simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7328 p hg
    simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7330 (p : Pattern) (guard : d1171 p = 1) : d673 p ≤ (0 : Int) + d600 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d673, d600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7273 p hg
    simpa only [d673, d600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d673, d600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7294 p hg
    simpa only [d673, d600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7331 (p : Pattern) (guard : d1171 p = 1) : d673 p ≤ (0 : Int) + d601 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7328 p hg
    simpa only [d601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7330 p hg
    simpa only [d601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7332 (p : Pattern) (guard : d1171 p = 1) : d673 p ≤ (0 : Int) + d602 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7329 p hg
    simpa only [d602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7331 p hg
    simpa only [d602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7333 (p : Pattern) (guard : d1171 p = 1) : d673 p ≤ (0 : Int) + d603 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d673, d603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7313 p hg
    simpa only [d673, d603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d673, d603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7292 p hg
    simpa only [d673, d603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7334 (p : Pattern) (guard : d1171 p = 1) : d673 p ≤ (0 : Int) + d604 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d673, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7281 p hg
    simpa only [d673, d604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d673, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7298 p hg
    simpa only [d673, d604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7335 (p : Pattern) (guard : d1171 p = 1) : d673 p ≤ (0 : Int) + d605 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7333 p hg
    simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7334 p hg
    simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7336 (p : Pattern) (guard : d1171 p = 1) : d673 p ≤ (0 : Int) + d606 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7335 p hg
    simpa only [d606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7331 p hg
    simpa only [d606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7337 (p : Pattern) (guard : d1171 p = 1) : d673 p ≤ (0 : Int) + d607 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7332 p hg
    simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7336 p hg
    simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7338 (p : Pattern) (guard : d1171 p = 1) : d674 p ≤ (0 : Int) + d608 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d674, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7286 p hg
    simpa only [d674, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d674, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7337 p hg
    simpa only [d674, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7339 (p : Pattern) (guard : d1171 p = 1) : d660 p ≤ (0 : Int) + d609 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7307 p hg
    simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7310 p hg
    simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7340 (p : Pattern) (guard : d1171 p = 1) : d660 p ≤ (0 : Int) + d610 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7339 p hg
    simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7310 p hg
    simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7341 (p : Pattern) (guard : d1171 p = 1) : d675 p ≤ (0 : Int) + d611 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d675, d611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7338 p hg
    simpa only [d675, d611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d675, d611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7340 p hg
    simpa only [d675, d611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7342 (p : Pattern) (guard : d1171 p = 1) : d673 p ≤ (0 : Int) + d612 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7333 p hg
    simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7328 p hg
    simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7343 (p : Pattern) (guard : d1171 p = 1) : d673 p ≤ (0 : Int) + d613 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7342 p hg
    simpa only [d613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7331 p hg
    simpa only [d613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7344 (p : Pattern) (guard : d1171 p = 1) : d676 p ≤ (0 : Int) + d614 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d676, d614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7331 p hg
    simpa only [d676, d614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d676, d614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7316 p hg
    simpa only [d676, d614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7345 (p : Pattern) (guard : d1171 p = 1) : d677 p ≤ (0 : Int) + d615 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d677, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7343 p hg
    simpa only [d677, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d677, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7344 p hg
    simpa only [d677, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7346 (p : Pattern) (guard : d1171 p = 1) : d678 p ≤ (0 : Int) + d616 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d678, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7318 p hg
    simpa only [d678, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d678, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7345 p hg
    simpa only [d678, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7347 (p : Pattern) (guard : d1171 p = 1) : d679 p ≤ (0 : Int) + d617 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d679, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7310 p hg
    simpa only [d679, d617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d679, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d679, d617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7348 (p : Pattern) (guard : d1171 p = 1) : d680 p ≤ (0 : Int) + d618 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d680, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7339 p hg
    simpa only [d680, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d680, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7347 p hg
    simpa only [d680, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7349 (p : Pattern) (guard : d1171 p = 1) : d659 p ≤ (0 : Int) + d619 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7306 p hg
    simpa only [d619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7316 p hg
    simpa only [d619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7350 (p : Pattern) (guard : d1171 p = 1) : d681 p ≤ (0 : Int) + d620 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d681, d620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7316 p hg
    simpa only [d681, d620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d681, d620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d681, d620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7351 (p : Pattern) (guard : d1171 p = 1) : d682 p ≤ (0 : Int) + d621 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d682, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7349 p hg
    simpa only [d682, d621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d682, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7350 p hg
    simpa only [d682, d621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7352 (p : Pattern) (guard : d1171 p = 1) : d683 p ≤ (0 : Int) + d622 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d683, d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7348 p hg
    simpa only [d683, d622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d683, d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7351 p hg
    simpa only [d683, d622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7353 (p : Pattern) (guard : d1171 p = 1) : d684 p ≤ (0 : Int) + d623 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d684, d623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7346 p hg
    simpa only [d684, d623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d684, d623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7352 p hg
    simpa only [d684, d623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7354 (p : Pattern) (guard : d1171 p = 1) : d685 p ≤ (0 : Int) + d624 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d685, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7341 p hg
    simpa only [d685, d624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d685, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7353 p hg
    simpa only [d685, d624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7355 (p : Pattern) (guard : d1171 p = 1) : d686 p ≤ (0 : Int) + d625 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d686, d625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7326 p hg
    simpa only [d686, d625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d686, d625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7354 p hg
    simpa only [d686, d625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7356 (p : Pattern) (guard : d1171 p = 1) : d654 p ≤ (0 : Int) + d626 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7314 p hg
    simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7283 p hg
    simpa only [d626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7357 (p : Pattern) (guard : d1171 p = 1) : d654 p ≤ (0 : Int) + d627 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7356 p hg
    simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7278 p hg
    simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7358 (p : Pattern) (guard : d1171 p = 1) : d654 p ≤ (0 : Int) + d628 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7279 p hg
    simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7357 p hg
    simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7359 (p : Pattern) (guard : d1171 p = 1) : d654 p ≤ (0 : Int) + d629 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7286 p hg
    simpa only [d629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7358 p hg
    simpa only [d629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7360 (p : Pattern) (guard : d1171 p = 1) : d658 p ≤ (0 : Int) + d630 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d658, d630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7359 p hg
    simpa only [d658, d630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d658, d630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7303 p hg
    simpa only [d658, d630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7361 (p : Pattern) (guard : d1171 p = 1) : d654 p ≤ (0 : Int) + d631 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7314 p hg
    simpa only [d631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7270 p hg
    simpa only [d631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7362 (p : Pattern) (guard : d1171 p = 1) : d654 p ≤ (0 : Int) + d632 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7361 p hg
    simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7278 p hg
    simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7363 (p : Pattern) (guard : d1171 p = 1) : d663 p ≤ (0 : Int) + d633 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d663, d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7278 p hg
    simpa only [d663, d633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d663, d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7316 p hg
    simpa only [d663, d633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7364 (p : Pattern) (guard : d1171 p = 1) : d664 p ≤ (0 : Int) + d634 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d664, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7362 p hg
    simpa only [d664, d634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d664, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7363 p hg
    simpa only [d664, d634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7365 (p : Pattern) (guard : d1171 p = 1) : d664 p ≤ (0 : Int) + d635 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7318 p hg
    simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7364 p hg
    simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7366 (p : Pattern) (guard : d1171 p = 1) : d687 p ≤ (0 : Int) + d636 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d687, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7365 p hg
    simpa only [d687, d636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d687, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7324 p hg
    simpa only [d687, d636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7367 (p : Pattern) (guard : d1171 p = 1) : d688 p ≤ (0 : Int) + d637 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d688, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7360 p hg
    simpa only [d688, d637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d688, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7366 p hg
    simpa only [d688, d637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7368 (p : Pattern) (guard : d1171 p = 1) : d7 p ≤ (0 : Int) + d638 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7281 p hg
    simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7273 p hg
    simpa only [d638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7369 (p : Pattern) (guard : d1171 p = 1) : d673 p ≤ (0 : Int) + d639 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d673, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7368 p hg
    simpa only [d673, d639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d673, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7298 p hg
    simpa only [d673, d639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7370 (p : Pattern) (guard : d1171 p = 1) : d673 p ≤ (0 : Int) + d640 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7328 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7369 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7371 (p : Pattern) (guard : d1171 p = 1) : d673 p ≤ (0 : Int) + d641 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7370 p hg
    simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7331 p hg
    simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7372 (p : Pattern) (guard : d1171 p = 1) : d673 p ≤ (0 : Int) + d642 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7343 p hg
    simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7371 p hg
    simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7373 (p : Pattern) (guard : d1171 p = 1) : d674 p ≤ (0 : Int) + d643 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d674, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7358 p hg
    simpa only [d674, d643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d674, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7372 p hg
    simpa only [d674, d643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7374 (p : Pattern) (guard : d1171 p = 1) : d659 p ≤ (0 : Int) + d644 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7349 p hg
    simpa only [d644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7316 p hg
    simpa only [d644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7375 (p : Pattern) (guard : d1171 p = 1) : d689 p ≤ (0 : Int) + d645 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d689, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7340 p hg
    simpa only [d689, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d689, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7374 p hg
    simpa only [d689, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7376 (p : Pattern) (guard : d1171 p = 1) : d690 p ≤ (0 : Int) + d646 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d690, d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7373 p hg
    simpa only [d690, d646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d690, d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7375 p hg
    simpa only [d690, d646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7377 (p : Pattern) (guard : d1171 p = 1) : d691 p ≤ (0 : Int) + d647 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d691, d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7364 p hg
    simpa only [d691, d647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d691, d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7323 p hg
    simpa only [d691, d647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7378 (p : Pattern) (guard : d1171 p = 1) : d692 p ≤ (0 : Int) + d648 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d692, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7351 p hg
    simpa only [d692, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d692, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d692, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7379 (p : Pattern) (guard : d1171 p = 1) : d693 p ≤ (0 : Int) + d649 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d693, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7377 p hg
    simpa only [d693, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d693, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7378 p hg
    simpa only [d693, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7380 (p : Pattern) (guard : d1171 p = 1) : d694 p ≤ (0 : Int) + d650 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d694, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7376 p hg
    simpa only [d694, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d694, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7379 p hg
    simpa only [d694, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7381 (p : Pattern) (guard : d1171 p = 1) : d695 p ≤ (0 : Int) + d651 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d695, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7367 p hg
    simpa only [d695, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d695, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7380 p hg
    simpa only [d695, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7382 (p : Pattern) (guard : d1171 p = 1) : d696 p ≤ (0 : Int) + d652 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d696, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7355 p hg
    simpa only [d696, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d696, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7381 p hg
    simpa only [d696, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7383 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (2 : Int) + d6 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7384 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7385 (p : Pattern) (guard : d1167 p = 1) : d7 p ≤ (2 : Int) + d6 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d7, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4306 p hg
    simpa only [d1167, d7, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d7, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7384 p hg
    simpa only [d1167, d7, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7386 (p : Pattern) (guard : d1412 p = 1) : d7 p ≤ (2 : Int) + d6 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7383 p hg
    simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7385 p hg
    simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7387 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7388 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7389 (p : Pattern) (guard : d1167 p = 1) : d13 p ≤ (2 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4315 p hg
    simpa only [d1167, d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7388 p hg
    simpa only [d1167, d13, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7390 (p : Pattern) (guard : d1412 p = 1) : d13 p ≤ (2 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7387 p hg
    simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7389 p hg
    simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7391 (p : Pattern) (guard : d1412 p = 1) : d653 p ≤ (2 : Int) + d1602 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d653, d1602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7386 p hg
    simpa only [d653, d1602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d653, d1602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7390 p hg
    simpa only [d653, d1602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7392 (p : Pattern) (guard : d1412 p = 1) : d654 p ≤ (2 : Int) + d1603 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d654, d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7386 p hg
    simpa only [d654, d1603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d654, d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7391 p hg
    simpa only [d654, d1603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7393 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (2 : Int) + d18 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7394 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d17 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7395 (p : Pattern) (guard : d1167 p = 1) : d7 p ≤ (2 : Int) + d18 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d7, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4306 p hg
    simpa only [d1167, d7, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d7, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7394 p hg
    simpa only [d1167, d7, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7396 (p : Pattern) (guard : d1412 p = 1) : d7 p ≤ (2 : Int) + d18 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7393 p hg
    simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7395 p hg
    simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7397 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (2 : Int) + d22 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7398 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d21 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7399 (p : Pattern) (guard : d1167 p = 1) : d13 p ≤ (2 : Int) + d22 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d13, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4315 p hg
    simpa only [d1167, d13, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d13, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7398 p hg
    simpa only [d1167, d13, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7400 (p : Pattern) (guard : d1412 p = 1) : d13 p ≤ (2 : Int) + d22 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7397 p hg
    simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7399 p hg
    simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7401 (p : Pattern) (guard : d1412 p = 1) : d653 p ≤ (2 : Int) + d1604 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d653, d1604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7396 p hg
    simpa only [d653, d1604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d653, d1604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7400 p hg
    simpa only [d653, d1604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7402 (p : Pattern) (guard : d1412 p = 1) : d654 p ≤ (2 : Int) + d1605 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d654, d1605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7396 p hg
    simpa only [d654, d1605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d654, d1605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7401 p hg
    simpa only [d654, d1605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7403 (p : Pattern) (guard : d1412 p = 1) : d654 p ≤ (2 : Int) + d1606 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7392 p hg
    simpa only [d1606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7402 p hg
    simpa only [d1606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7404 (p : Pattern) (guard : d1412 p = 1) : d654 p ≤ (2 : Int) + d1607 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7392 p hg
    simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7403 p hg
    simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7405 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (2 : Int) + d31 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7406 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d30 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7407 (p : Pattern) (guard : d1167 p = 1) : d7 p ≤ (2 : Int) + d31 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d7, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4306 p hg
    simpa only [d1167, d7, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d7, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7406 p hg
    simpa only [d1167, d7, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7408 (p : Pattern) (guard : d1412 p = 1) : d7 p ≤ (2 : Int) + d31 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7405 p hg
    simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7407 p hg
    simpa only [d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7409 (p : Pattern) (guard : d1412 p = 1) : d653 p ≤ (2 : Int) + d1608 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d653, d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7408 p hg
    simpa only [d653, d1608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d653, d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7400 p hg
    simpa only [d653, d1608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7410 (p : Pattern) (guard : d1412 p = 1) : d654 p ≤ (2 : Int) + d1609 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d654, d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7408 p hg
    simpa only [d654, d1609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d654, d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7409 p hg
    simpa only [d654, d1609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7411 (p : Pattern) (guard : d1412 p = 1) : d654 p ≤ (2 : Int) + d1610 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7392 p hg
    simpa only [d1610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7410 p hg
    simpa only [d1610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7412 (p : Pattern) (guard : d1412 p = 1) : d654 p ≤ (2 : Int) + d1611 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7411 p hg
    simpa only [d1611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7403 p hg
    simpa only [d1611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7413 (p : Pattern) (guard : d1412 p = 1) : d654 p ≤ (2 : Int) + d1612 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7404 p hg
    simpa only [d1612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7412 p hg
    simpa only [d1612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7414 (p : Pattern) (guard : d1412 p = 1) : d653 p ≤ (2 : Int) + d1613 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7391 p hg
    simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7401 p hg
    simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7415 (p : Pattern) (guard : d1412 p = 1) : d653 p ≤ (2 : Int) + d1614 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7391 p hg
    simpa only [d1614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7414 p hg
    simpa only [d1614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7416 (p : Pattern) (guard : d1412 p = 1) : d653 p ≤ (2 : Int) + d1615 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7391 p hg
    simpa only [d1615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7409 p hg
    simpa only [d1615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7417 (p : Pattern) (guard : d1412 p = 1) : d653 p ≤ (2 : Int) + d1616 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7416 p hg
    simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7414 p hg
    simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7418 (p : Pattern) (guard : d1412 p = 1) : d653 p ≤ (2 : Int) + d1617 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1412 p = 1 := by simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7415 p hg
    simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1412 p = 1 := by simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7417 p hg
    simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7419 (p : Pattern) (guard : d1412 p = 1) : d2 p ≤ (2 : Int) + d2 p := by
  omega
end NetHack.Sokoban32Refined
