import NetHack.Soko22Hazard87.Compare048
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare12250 (p : Pattern) (guard : d160557 p = 1) : d47765 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160556 p = 1 := by simpa only [d160557, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12249 p hg
    simpa only [d160557, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160557, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11050 p hg
    simpa only [d160557, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12251 (p : Pattern) (guard : d160558 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160558, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11033 p hg
    simpa only [d160558, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160557 p = 1 := by simpa only [d160558, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12250 p hg
    simpa only [d160558, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12252 (p : Pattern) (guard : d160559 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160554 p = 1 := by simpa only [d160559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12243 p hg
    simpa only [d160559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160558 p = 1 := by simpa only [d160559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12251 p hg
    simpa only [d160559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12253 (p : Pattern) (guard : d160560 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160559 p = 1 := by simpa only [d160560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12252 p hg
    simpa only [d160560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12254 (p : Pattern) (guard : d160561 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160560 p = 1 := by simpa only [d160561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12253 p hg
    simpa only [d160561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12255 (p : Pattern) (guard : d160575 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160561 p = 1 := by simpa only [d160575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12254 p hg
    simpa only [d160575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12256 (p : Pattern) (guard : d160646 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160645 p = 1 := by simpa only [d160646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12247 p hg
    simpa only [d160646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160575 p = 1 := by simpa only [d160646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12255 p hg
    simpa only [d160646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12257 (p : Pattern) (guard : d160647 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160646 p = 1 := by simpa only [d160647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12256 p hg
    simpa only [d160647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12258 (p : Pattern) (guard : d160624 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160554 p = 1 := by simpa only [d160624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12243 p hg
    simpa only [d160624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12259 (p : Pattern) (guard : d160625 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160624 p = 1 := by simpa only [d160625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12258 p hg
    simpa only [d160625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12260 (p : Pattern) (guard : d160626 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160625 p = 1 := by simpa only [d160626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12259 p hg
    simpa only [d160626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12261 (p : Pattern) (guard : d160648 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160626 p = 1 := by simpa only [d160648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12260 p hg
    simpa only [d160648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12262 (p : Pattern) (guard : d160649 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160648 p = 1 := by simpa only [d160649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12261 p hg
    simpa only [d160649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12263 (p : Pattern) (guard : d160650 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160649 p = 1 := by simpa only [d160650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12262 p hg
    simpa only [d160650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12264 (p : Pattern) (guard : d160651 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160647 p = 1 := by simpa only [d160651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12257 p hg
    simpa only [d160651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160650 p = 1 := by simpa only [d160651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12263 p hg
    simpa only [d160651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12265 (p : Pattern) (guard : d160672 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160651 p = 1 := by simpa only [d160672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12264 p hg
    simpa only [d160672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12266 (p : Pattern) (guard : d160673 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160672 p = 1 := by simpa only [d160673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12265 p hg
    simpa only [d160673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12267 (p : Pattern) (guard : d160674 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160674, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160674, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160673 p = 1 := by simpa only [d160674, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12266 p hg
    simpa only [d160674, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12268 (p : Pattern) (guard : d160675 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d160675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160674 p = 1 := by simpa only [d160675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12267 p hg
    simpa only [d160675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12269 (p : Pattern) (guard : d160563 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160558 p = 1 := by simpa only [d160563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12251 p hg
    simpa only [d160563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12270 (p : Pattern) (guard : d160564 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160563 p = 1 := by simpa only [d160564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12269 p hg
    simpa only [d160564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12271 (p : Pattern) (guard : d160565 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160564 p = 1 := by simpa only [d160565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12270 p hg
    simpa only [d160565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12272 (p : Pattern) (guard : d160576 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160565 p = 1 := by simpa only [d160576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12271 p hg
    simpa only [d160576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12273 (p : Pattern) (guard : d160662 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160576 p = 1 := by simpa only [d160662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12272 p hg
    simpa only [d160662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12274 (p : Pattern) (guard : d160663 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160662 p = 1 := by simpa only [d160663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12273 p hg
    simpa only [d160663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12275 (p : Pattern) (guard : d160664 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160663 p = 1 := by simpa only [d160664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12274 p hg
    simpa only [d160664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12276 (p : Pattern) (guard : d160665 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160664 p = 1 := by simpa only [d160665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12275 p hg
    simpa only [d160665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12277 (p : Pattern) (guard : d160666 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160665 p = 1 := by simpa only [d160666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12276 p hg
    simpa only [d160666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12278 (p : Pattern) (guard : d160676 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160676, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160676, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160666 p = 1 := by simpa only [d160676, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12277 p hg
    simpa only [d160676, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12279 (p : Pattern) (guard : d160677 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d160677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160676 p = 1 := by simpa only [d160677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12278 p hg
    simpa only [d160677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12280 (p : Pattern) (guard : d160678 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160675 p = 1 := by simpa only [d160678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12268 p hg
    simpa only [d160678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160677 p = 1 := by simpa only [d160678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12279 p hg
    simpa only [d160678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12281 (p : Pattern) (guard : d160679 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 51 with
  | false =>
    have hg : d160678 p = 1 := by simpa only [d160679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12280 p hg
    simpa only [d160679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d160679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12282 (p : Pattern) (guard : d160680 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 50 with
  | false =>
    have hg : d160679 p = 1 := by simpa only [d160680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12281 p hg
    simpa only [d160680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d160680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12283 (p : Pattern) (guard : d160681 p = 1) : d47768 p ≤ (-1 : Int) + d159776 p := by
  cases selected : p 49 with
  | false =>
    have hg : d160671 p = 1 := by simpa only [d160681, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12195 p hg
    simpa only [d160681, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160680 p = 1 := by simpa only [d160681, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12282 p hg
    simpa only [d160681, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12284 (p : Pattern) (guard : d1857 p = 1) : d47652 p ≤ (-1 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1857, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11073 p hg
    simpa only [d1857, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1554 p = 1 := by simpa only [d1857, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6951 p hg
    simpa only [d1857, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12285 (p : Pattern) (guard : d1858 p = 1) : d47798 p ≤ (-1 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1857 p = 1 := by simpa only [d1858, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12284 p hg
    simpa only [d1858, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1555 p = 1 := by simpa only [d1858, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6953 p hg
    simpa only [d1858, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12286 (p : Pattern) (guard : d1859 p = 1) : d47799 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1858 p = 1 := by simpa only [d1859, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12285 p hg
    simpa only [d1859, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1556 p = 1 := by simpa only [d1859, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6972 p hg
    simpa only [d1859, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12287 (p : Pattern) (guard : d1860 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1859 p = 1 := by simpa only [d1860, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12286 p hg
    simpa only [d1860, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1860, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11077 p hg
    simpa only [d1860, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12288 (p : Pattern) (guard : d160682 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1860 p = 1 := by simpa only [d160682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12287 p hg
    simpa only [d160682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12289 (p : Pattern) (guard : d160683 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160682 p = 1 := by simpa only [d160683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12288 p hg
    simpa only [d160683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12290 (p : Pattern) (guard : d1862 p = 1) : d47652 p ≤ (-1 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1862, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11073 p hg
    simpa only [d1862, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1569 p = 1 := by simpa only [d1862, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6986 p hg
    simpa only [d1862, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12291 (p : Pattern) (guard : d1863 p = 1) : d47798 p ≤ (-1 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1862 p = 1 := by simpa only [d1863, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12290 p hg
    simpa only [d1863, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1570 p = 1 := by simpa only [d1863, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6988 p hg
    simpa only [d1863, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12292 (p : Pattern) (guard : d1864 p = 1) : d47799 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1863 p = 1 := by simpa only [d1864, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12291 p hg
    simpa only [d1864, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1571 p = 1 := by simpa only [d1864, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7002 p hg
    simpa only [d1864, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12293 (p : Pattern) (guard : d1865 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1864 p = 1 := by simpa only [d1865, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12292 p hg
    simpa only [d1865, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1865, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11077 p hg
    simpa only [d1865, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12294 (p : Pattern) (guard : d160684 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1865 p = 1 := by simpa only [d160684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12293 p hg
    simpa only [d160684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12295 (p : Pattern) (guard : d160685 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160684 p = 1 := by simpa only [d160685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12294 p hg
    simpa only [d160685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12296 (p : Pattern) (guard : d160686 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160683 p = 1 := by simpa only [d160686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12289 p hg
    simpa only [d160686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160685 p = 1 := by simpa only [d160686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12295 p hg
    simpa only [d160686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12297 (p : Pattern) (guard : d160687 p = 1) : d47804 p ≤ (-1 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160687, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11071 p hg
    simpa only [d160687, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160686 p = 1 := by simpa only [d160687, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12296 p hg
    simpa only [d160687, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12298 (p : Pattern) (guard : d160688 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160688, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11070 p hg
    simpa only [d160688, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160687 p = 1 := by simpa only [d160688, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12297 p hg
    simpa only [d160688, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12299 (p : Pattern) (guard : d10057 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5122 p = 1 := by simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7067 p hg
    simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12300 (p : Pattern) (guard : d10058 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d10057 p = 1 := by simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12299 p hg
    simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12301 (p : Pattern) (guard : d10080 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6942 p hg
    simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10058 p = 1 := by simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12300 p hg
    simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12302 (p : Pattern) (guard : d10081 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1550 p = 1 := by simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6947 p hg
    simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12303 (p : Pattern) (guard : d10082 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d10080 p = 1 := by simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12301 p hg
    simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10081 p = 1 := by simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12302 p hg
    simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12304 (p : Pattern) (guard : d10083 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10082 p = 1 := by simpa only [d10083, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12303 p hg
    simpa only [d10083, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10083, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d10083, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12305 (p : Pattern) (guard : d13350 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10083 p = 1 := by simpa only [d13350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12304 p hg
    simpa only [d13350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4533 p hg
    simpa only [d13350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12306 (p : Pattern) (guard : d13490 p = 1) : d47652 p ≤ (-1 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d13490, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11073 p hg
    simpa only [d13490, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13350 p = 1 := by simpa only [d13490, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12305 p hg
    simpa only [d13490, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12307 (p : Pattern) (guard : d13351 p = 1) : d47797 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d13350 p = 1 := by simpa only [d13351, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12127 p hg
    simpa only [d13351, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13351, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d13351, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12308 (p : Pattern) (guard : d13491 p = 1) : d47798 p ≤ (-1 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d13490 p = 1 := by simpa only [d13491, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12306 p hg
    simpa only [d13491, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13351 p = 1 := by simpa only [d13491, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12307 p hg
    simpa only [d13491, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12309 (p : Pattern) (guard : d10057 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5122 p = 1 := by simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7083 p hg
    simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12310 (p : Pattern) (guard : d10058 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d10057 p = 1 := by simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12309 p hg
    simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12311 (p : Pattern) (guard : d10080 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6961 p hg
    simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10058 p = 1 := by simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12310 p hg
    simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12312 (p : Pattern) (guard : d10081 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1550 p = 1 := by simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6966 p hg
    simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12313 (p : Pattern) (guard : d10082 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d10080 p = 1 := by simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12311 p hg
    simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10081 p = 1 := by simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12312 p hg
    simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12314 (p : Pattern) (guard : d10083 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10082 p = 1 := by simpa only [d10083, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12313 p hg
    simpa only [d10083, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10083, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d10083, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12315 (p : Pattern) (guard : d13350 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10083 p = 1 := by simpa only [d13350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12314 p hg
    simpa only [d13350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4551 p hg
    simpa only [d13350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12316 (p : Pattern) (guard : d13351 p = 1) : d47682 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d13350 p = 1 := by simpa only [d13351, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12315 p hg
    simpa only [d13351, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13351, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d13351, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12317 (p : Pattern) (guard : d13352 p = 1) : d47683 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d13351 p = 1 := by simpa only [d13352, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12316 p hg
    simpa only [d13352, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13352, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d13352, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12318 (p : Pattern) (guard : d13492 p = 1) : d47799 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d13491 p = 1 := by simpa only [d13492, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12308 p hg
    simpa only [d13492, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13352 p = 1 := by simpa only [d13492, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12317 p hg
    simpa only [d13492, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12319 (p : Pattern) (guard : d13493 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13492 p = 1 := by simpa only [d13493, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12318 p hg
    simpa only [d13493, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13493, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11077 p hg
    simpa only [d13493, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12320 (p : Pattern) (guard : d160689 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13493 p = 1 := by simpa only [d160689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12319 p hg
    simpa only [d160689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12321 (p : Pattern) (guard : d160690 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160689 p = 1 := by simpa only [d160690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12320 p hg
    simpa only [d160690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12322 (p : Pattern) (guard : d160691 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160685 p = 1 := by simpa only [d160691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12295 p hg
    simpa only [d160691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160690 p = 1 := by simpa only [d160691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12321 p hg
    simpa only [d160691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12323 (p : Pattern) (guard : d160692 p = 1) : d47804 p ≤ (-1 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160692, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11071 p hg
    simpa only [d160692, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160691 p = 1 := by simpa only [d160692, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12322 p hg
    simpa only [d160692, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12324 (p : Pattern) (guard : d160693 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160693, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11070 p hg
    simpa only [d160693, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160692 p = 1 := by simpa only [d160693, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12323 p hg
    simpa only [d160693, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12325 (p : Pattern) (guard : d160694 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160688 p = 1 := by simpa only [d160694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12298 p hg
    simpa only [d160694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160693 p = 1 := by simpa only [d160694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12324 p hg
    simpa only [d160694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12326 (p : Pattern) (guard : d1868 p = 1) : d47652 p ≤ (-1 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1868, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11073 p hg
    simpa only [d1868, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1581 p = 1 := by simpa only [d1868, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7013 p hg
    simpa only [d1868, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12327 (p : Pattern) (guard : d1869 p = 1) : d47798 p ≤ (-1 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1868 p = 1 := by simpa only [d1869, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12326 p hg
    simpa only [d1869, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1582 p = 1 := by simpa only [d1869, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7015 p hg
    simpa only [d1869, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12328 (p : Pattern) (guard : d1870 p = 1) : d47799 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1869 p = 1 := by simpa only [d1870, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12327 p hg
    simpa only [d1870, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1583 p = 1 := by simpa only [d1870, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7025 p hg
    simpa only [d1870, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12329 (p : Pattern) (guard : d1871 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1870 p = 1 := by simpa only [d1871, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12328 p hg
    simpa only [d1871, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1871, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11077 p hg
    simpa only [d1871, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12330 (p : Pattern) (guard : d160695 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1871 p = 1 := by simpa only [d160695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12329 p hg
    simpa only [d160695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12331 (p : Pattern) (guard : d160696 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160695 p = 1 := by simpa only [d160696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12330 p hg
    simpa only [d160696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12332 (p : Pattern) (guard : d160697 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160685 p = 1 := by simpa only [d160697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12295 p hg
    simpa only [d160697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160696 p = 1 := by simpa only [d160697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12331 p hg
    simpa only [d160697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12333 (p : Pattern) (guard : d160698 p = 1) : d47804 p ≤ (-1 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160698, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11071 p hg
    simpa only [d160698, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160697 p = 1 := by simpa only [d160698, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12332 p hg
    simpa only [d160698, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12334 (p : Pattern) (guard : d160699 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160699, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11070 p hg
    simpa only [d160699, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160698 p = 1 := by simpa only [d160699, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12333 p hg
    simpa only [d160699, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12335 (p : Pattern) (guard : d160700 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160696 p = 1 := by simpa only [d160700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12331 p hg
    simpa only [d160700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12336 (p : Pattern) (guard : d160701 p = 1) : d47804 p ≤ (-1 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160701, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11071 p hg
    simpa only [d160701, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160700 p = 1 := by simpa only [d160701, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12335 p hg
    simpa only [d160701, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12337 (p : Pattern) (guard : d160702 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160702, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11070 p hg
    simpa only [d160702, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160701 p = 1 := by simpa only [d160702, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12336 p hg
    simpa only [d160702, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12338 (p : Pattern) (guard : d160703 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160699 p = 1 := by simpa only [d160703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12334 p hg
    simpa only [d160703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160702 p = 1 := by simpa only [d160703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12337 p hg
    simpa only [d160703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12339 (p : Pattern) (guard : d160704 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160694 p = 1 := by simpa only [d160704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12325 p hg
    simpa only [d160704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160703 p = 1 := by simpa only [d160704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12338 p hg
    simpa only [d160704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12340 (p : Pattern) (guard : d160705 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160704 p = 1 := by simpa only [d160705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12339 p hg
    simpa only [d160705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d160705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12341 (p : Pattern) (guard : d160706 p = 1) : d47807 p ≤ (-1 : Int) + d159781 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160705 p = 1 := by simpa only [d160706, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12340 p hg
    simpa only [d160706, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160706, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11088 p hg
    simpa only [d160706, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12342 (p : Pattern) (guard : d160707 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160707, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160707, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160706 p = 1 := by simpa only [d160707, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12341 p hg
    simpa only [d160707, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12343 (p : Pattern) (guard : d160708 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160702 p = 1 := by simpa only [d160708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12337 p hg
    simpa only [d160708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d160708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12344 (p : Pattern) (guard : d160709 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160703 p = 1 := by simpa only [d160709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12338 p hg
    simpa only [d160709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160708 p = 1 := by simpa only [d160709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12343 p hg
    simpa only [d160709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12345 (p : Pattern) (guard : d160710 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160709 p = 1 := by simpa only [d160710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12344 p hg
    simpa only [d160710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d160710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12346 (p : Pattern) (guard : d160711 p = 1) : d47807 p ≤ (-1 : Int) + d159781 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160710 p = 1 := by simpa only [d160711, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12345 p hg
    simpa only [d160711, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160711, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11088 p hg
    simpa only [d160711, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12347 (p : Pattern) (guard : d160712 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160712, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160712, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160711 p = 1 := by simpa only [d160712, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12346 p hg
    simpa only [d160712, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12348 (p : Pattern) (guard : d160713 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160707 p = 1 := by simpa only [d160713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12342 p hg
    simpa only [d160713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160712 p = 1 := by simpa only [d160713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12347 p hg
    simpa only [d160713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12349 (p : Pattern) (guard : d160714 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160713 p = 1 := by simpa only [d160714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12348 p hg
    simpa only [d160714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12350 (p : Pattern) (guard : d160715 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160714 p = 1 := by simpa only [d160715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12349 p hg
    simpa only [d160715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12351 (p : Pattern) (guard : d160716 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160715 p = 1 := by simpa only [d160716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12350 p hg
    simpa only [d160716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12352 (p : Pattern) (guard : d160717 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160708 p = 1 := by simpa only [d160717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12343 p hg
    simpa only [d160717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d160717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12353 (p : Pattern) (guard : d160718 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160717 p = 1 := by simpa only [d160718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12352 p hg
    simpa only [d160718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d160718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12354 (p : Pattern) (guard : d160719 p = 1) : d47807 p ≤ (-1 : Int) + d159781 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160718 p = 1 := by simpa only [d160719, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12353 p hg
    simpa only [d160719, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160719, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11088 p hg
    simpa only [d160719, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12355 (p : Pattern) (guard : d160720 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160720, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160720, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160719 p = 1 := by simpa only [d160720, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12354 p hg
    simpa only [d160720, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12356 (p : Pattern) (guard : d160721 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160712 p = 1 := by simpa only [d160721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12347 p hg
    simpa only [d160721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160720 p = 1 := by simpa only [d160721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12355 p hg
    simpa only [d160721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12357 (p : Pattern) (guard : d160722 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160721 p = 1 := by simpa only [d160722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12356 p hg
    simpa only [d160722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12358 (p : Pattern) (guard : d160723 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160722 p = 1 := by simpa only [d160723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12357 p hg
    simpa only [d160723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12359 (p : Pattern) (guard : d160724 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160723 p = 1 := by simpa only [d160724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12358 p hg
    simpa only [d160724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12360 (p : Pattern) (guard : d160725 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160716 p = 1 := by simpa only [d160725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12351 p hg
    simpa only [d160725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160724 p = 1 := by simpa only [d160725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12359 p hg
    simpa only [d160725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12361 (p : Pattern) (guard : d160726 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160725 p = 1 := by simpa only [d160726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12360 p hg
    simpa only [d160726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12362 (p : Pattern) (guard : d160727 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160712 p = 1 := by simpa only [d160727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12347 p hg
    simpa only [d160727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12363 (p : Pattern) (guard : d160728 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160727 p = 1 := by simpa only [d160728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12362 p hg
    simpa only [d160728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12364 (p : Pattern) (guard : d160729 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160728 p = 1 := by simpa only [d160729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12363 p hg
    simpa only [d160729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12365 (p : Pattern) (guard : d160730 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160729 p = 1 := by simpa only [d160730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12364 p hg
    simpa only [d160730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12366 (p : Pattern) (guard : d160731 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160730 p = 1 := by simpa only [d160731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12365 p hg
    simpa only [d160731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12367 (p : Pattern) (guard : d160732 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160731 p = 1 := by simpa only [d160732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12366 p hg
    simpa only [d160732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12368 (p : Pattern) (guard : d160733 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160726 p = 1 := by simpa only [d160733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12361 p hg
    simpa only [d160733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160732 p = 1 := by simpa only [d160733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12367 p hg
    simpa only [d160733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12369 (p : Pattern) (guard : d160734 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160733 p = 1 := by simpa only [d160734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12368 p hg
    simpa only [d160734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12370 (p : Pattern) (guard : d160735 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160734 p = 1 := by simpa only [d160735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12369 p hg
    simpa only [d160735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12371 (p : Pattern) (guard : d160736 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160736, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160736, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160735 p = 1 := by simpa only [d160736, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12370 p hg
    simpa only [d160736, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12372 (p : Pattern) (guard : d160737 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d160737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160736 p = 1 := by simpa only [d160737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12371 p hg
    simpa only [d160737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12373 (p : Pattern) (guard : d160738 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160720 p = 1 := by simpa only [d160738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12355 p hg
    simpa only [d160738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12374 (p : Pattern) (guard : d160739 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160738 p = 1 := by simpa only [d160739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12373 p hg
    simpa only [d160739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12375 (p : Pattern) (guard : d160740 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160739 p = 1 := by simpa only [d160740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12374 p hg
    simpa only [d160740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12376 (p : Pattern) (guard : d160741 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160740 p = 1 := by simpa only [d160741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12375 p hg
    simpa only [d160741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12377 (p : Pattern) (guard : d160742 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160741 p = 1 := by simpa only [d160742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12376 p hg
    simpa only [d160742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12378 (p : Pattern) (guard : d160743 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160742 p = 1 := by simpa only [d160743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12377 p hg
    simpa only [d160743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12379 (p : Pattern) (guard : d160744 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160743 p = 1 := by simpa only [d160744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12378 p hg
    simpa only [d160744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12380 (p : Pattern) (guard : d160745 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160744 p = 1 := by simpa only [d160745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12379 p hg
    simpa only [d160745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12381 (p : Pattern) (guard : d160746 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160745 p = 1 := by simpa only [d160746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12380 p hg
    simpa only [d160746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12382 (p : Pattern) (guard : d160747 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160747, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160747, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160746 p = 1 := by simpa only [d160747, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12381 p hg
    simpa only [d160747, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12383 (p : Pattern) (guard : d160748 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d160748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160747 p = 1 := by simpa only [d160748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12382 p hg
    simpa only [d160748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12384 (p : Pattern) (guard : d160749 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160737 p = 1 := by simpa only [d160749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12372 p hg
    simpa only [d160749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160748 p = 1 := by simpa only [d160749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12383 p hg
    simpa only [d160749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12385 (p : Pattern) (guard : d160750 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 51 with
  | false =>
    have hg : d160749 p = 1 := by simpa only [d160750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12384 p hg
    simpa only [d160750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d160750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12386 (p : Pattern) (guard : d160751 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 50 with
  | false =>
    have hg : d160750 p = 1 := by simpa only [d160751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12385 p hg
    simpa only [d160751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d160751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12387 (p : Pattern) (guard : d160752 p = 1) : d47865 p ≤ (-1 : Int) + d159794 p := by
  cases selected : p 49 with
  | false =>
    have hg : d160751 p = 1 := by simpa only [d160752, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12386 p hg
    simpa only [d160752, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160752, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11105 p hg
    simpa only [d160752, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12388 (p : Pattern) (guard : d160753 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 48 with
  | false =>
    have hg : d160681 p = 1 := by simpa only [d160753, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12283 p hg
    simpa only [d160753, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160752 p = 1 := by simpa only [d160753, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12387 p hg
    simpa only [d160753, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12389 (p : Pattern) (guard : d160754 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160753 p = 1 := by simpa only [d160754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12388 p hg
    simpa only [d160754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12390 (p : Pattern) (guard : d160755 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160754 p = 1 := by simpa only [d160755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12389 p hg
    simpa only [d160755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12391 (p : Pattern) (guard : d160756 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160755 p = 1 := by simpa only [d160756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12390 p hg
    simpa only [d160756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12392 (p : Pattern) (guard : d160757 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160756 p = 1 := by simpa only [d160757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12391 p hg
    simpa only [d160757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12393 (p : Pattern) (guard : d160758 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160757 p = 1 := by simpa only [d160758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12392 p hg
    simpa only [d160758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12394 (p : Pattern) (guard : d160759 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160758 p = 1 := by simpa only [d160759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12393 p hg
    simpa only [d160759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12395 (p : Pattern) (guard : d160760 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160759 p = 1 := by simpa only [d160760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12394 p hg
    simpa only [d160760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12396 (p : Pattern) (guard : d160761 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160760 p = 1 := by simpa only [d160761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12395 p hg
    simpa only [d160761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12397 (p : Pattern) (guard : d160762 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160761 p = 1 := by simpa only [d160762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12396 p hg
    simpa only [d160762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12398 (p : Pattern) (guard : d160763 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d160538 p = 1 := by simpa only [d160763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12045 p hg
    simpa only [d160763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160762 p = 1 := by simpa only [d160763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12397 p hg
    simpa only [d160763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12399 (p : Pattern) (guard : d2055 p = 1) : d47664 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2055, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10994 p hg
    simpa only [d2055, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2054 p = 1 := by simpa only [d2055, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7226 p hg
    simpa only [d2055, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12400 (p : Pattern) (guard : d2056 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2055 p = 1 := by simpa only [d2056, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12399 p hg
    simpa only [d2056, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2056, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10996 p hg
    simpa only [d2056, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12401 (p : Pattern) (guard : d160764 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2056 p = 1 := by simpa only [d160764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12400 p hg
    simpa only [d160764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12402 (p : Pattern) (guard : d160765 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160764 p = 1 := by simpa only [d160765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12401 p hg
    simpa only [d160765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12403 (p : Pattern) (guard : d2067 p = 1) : d47664 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2067, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10994 p hg
    simpa only [d2067, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2066 p = 1 := by simpa only [d2067, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7238 p hg
    simpa only [d2067, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12404 (p : Pattern) (guard : d2068 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2067 p = 1 := by simpa only [d2068, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12403 p hg
    simpa only [d2068, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2068, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10996 p hg
    simpa only [d2068, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12405 (p : Pattern) (guard : d160766 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2068 p = 1 := by simpa only [d160766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12404 p hg
    simpa only [d160766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12406 (p : Pattern) (guard : d160767 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160766 p = 1 := by simpa only [d160767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12405 p hg
    simpa only [d160767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12407 (p : Pattern) (guard : d160768 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160765 p = 1 := by simpa only [d160768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12402 p hg
    simpa only [d160768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160767 p = 1 := by simpa only [d160768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12406 p hg
    simpa only [d160768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12408 (p : Pattern) (guard : d160769 p = 1) : d47686 p ≤ (-1 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160769, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10992 p hg
    simpa only [d160769, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160768 p = 1 := by simpa only [d160769, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12407 p hg
    simpa only [d160769, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12409 (p : Pattern) (guard : d160770 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160770, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10991 p hg
    simpa only [d160770, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160769 p = 1 := by simpa only [d160770, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12408 p hg
    simpa only [d160770, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12410 (p : Pattern) (guard : d160771 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160767 p = 1 := by simpa only [d160771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12406 p hg
    simpa only [d160771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12411 (p : Pattern) (guard : d160772 p = 1) : d47686 p ≤ (-1 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160772, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10992 p hg
    simpa only [d160772, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160771 p = 1 := by simpa only [d160772, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12410 p hg
    simpa only [d160772, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12412 (p : Pattern) (guard : d160773 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160773, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10991 p hg
    simpa only [d160773, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160772 p = 1 := by simpa only [d160773, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12411 p hg
    simpa only [d160773, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12413 (p : Pattern) (guard : d160774 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160770 p = 1 := by simpa only [d160774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12409 p hg
    simpa only [d160774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160773 p = 1 := by simpa only [d160774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12412 p hg
    simpa only [d160774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12414 (p : Pattern) (guard : d160775 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160773 p = 1 := by simpa only [d160775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12412 p hg
    simpa only [d160775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d160775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12415 (p : Pattern) (guard : d160776 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160774 p = 1 := by simpa only [d160776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12413 p hg
    simpa only [d160776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160775 p = 1 := by simpa only [d160776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12414 p hg
    simpa only [d160776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12416 (p : Pattern) (guard : d160777 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160776 p = 1 := by simpa only [d160777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12415 p hg
    simpa only [d160777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d160777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12417 (p : Pattern) (guard : d160778 p = 1) : d47699 p ≤ (-1 : Int) + d159769 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160777 p = 1 := by simpa only [d160778, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12416 p hg
    simpa only [d160778, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160778, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11007 p hg
    simpa only [d160778, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12418 (p : Pattern) (guard : d160779 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160779, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160779, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160778 p = 1 := by simpa only [d160779, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12417 p hg
    simpa only [d160779, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12419 (p : Pattern) (guard : d160780 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160775 p = 1 := by simpa only [d160780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12414 p hg
    simpa only [d160780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d160780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12420 (p : Pattern) (guard : d160781 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160780 p = 1 := by simpa only [d160781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12419 p hg
    simpa only [d160781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d160781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12421 (p : Pattern) (guard : d160782 p = 1) : d47699 p ≤ (-1 : Int) + d159769 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160781 p = 1 := by simpa only [d160782, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12420 p hg
    simpa only [d160782, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160782, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11007 p hg
    simpa only [d160782, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12422 (p : Pattern) (guard : d160783 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160783, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160783, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160782 p = 1 := by simpa only [d160783, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12421 p hg
    simpa only [d160783, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12423 (p : Pattern) (guard : d160784 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160779 p = 1 := by simpa only [d160784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12418 p hg
    simpa only [d160784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160783 p = 1 := by simpa only [d160784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12422 p hg
    simpa only [d160784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12424 (p : Pattern) (guard : d160785 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160784 p = 1 := by simpa only [d160785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12423 p hg
    simpa only [d160785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12425 (p : Pattern) (guard : d160786 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160785 p = 1 := by simpa only [d160786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12424 p hg
    simpa only [d160786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12426 (p : Pattern) (guard : d160787 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160786 p = 1 := by simpa only [d160787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12425 p hg
    simpa only [d160787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12427 (p : Pattern) (guard : d160788 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160783 p = 1 := by simpa only [d160788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12422 p hg
    simpa only [d160788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12428 (p : Pattern) (guard : d160789 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160788 p = 1 := by simpa only [d160789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12427 p hg
    simpa only [d160789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12429 (p : Pattern) (guard : d160790 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160789 p = 1 := by simpa only [d160790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12428 p hg
    simpa only [d160790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12430 (p : Pattern) (guard : d160791 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160790 p = 1 := by simpa only [d160791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12429 p hg
    simpa only [d160791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12431 (p : Pattern) (guard : d160792 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160787 p = 1 := by simpa only [d160792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12426 p hg
    simpa only [d160792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160791 p = 1 := by simpa only [d160792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12430 p hg
    simpa only [d160792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12432 (p : Pattern) (guard : d160793 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160792 p = 1 := by simpa only [d160793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12431 p hg
    simpa only [d160793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12433 (p : Pattern) (guard : d160794 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160793 p = 1 := by simpa only [d160794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12432 p hg
    simpa only [d160794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12434 (p : Pattern) (guard : d160795 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160794 p = 1 := by simpa only [d160795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12433 p hg
    simpa only [d160795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12435 (p : Pattern) (guard : d160796 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160795 p = 1 := by simpa only [d160796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12434 p hg
    simpa only [d160796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12436 (p : Pattern) (guard : d160797 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160796 p = 1 := by simpa only [d160797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12435 p hg
    simpa only [d160797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12437 (p : Pattern) (guard : d160798 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160797 p = 1 := by simpa only [d160798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12436 p hg
    simpa only [d160798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12438 (p : Pattern) (guard : d160799 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160798 p = 1 := by simpa only [d160799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12437 p hg
    simpa only [d160799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12439 (p : Pattern) (guard : d160800 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160786 p = 1 := by simpa only [d160800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12425 p hg
    simpa only [d160800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12440 (p : Pattern) (guard : d160801 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160790 p = 1 := by simpa only [d160801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12429 p hg
    simpa only [d160801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12441 (p : Pattern) (guard : d160802 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160800 p = 1 := by simpa only [d160802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12439 p hg
    simpa only [d160802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160801 p = 1 := by simpa only [d160802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12440 p hg
    simpa only [d160802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12442 (p : Pattern) (guard : d160803 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160802 p = 1 := by simpa only [d160803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12441 p hg
    simpa only [d160803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12443 (p : Pattern) (guard : d160804 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160803 p = 1 := by simpa only [d160804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12442 p hg
    simpa only [d160804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12444 (p : Pattern) (guard : d160805 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160804 p = 1 := by simpa only [d160805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12443 p hg
    simpa only [d160805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12445 (p : Pattern) (guard : d160806 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160805 p = 1 := by simpa only [d160806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12444 p hg
    simpa only [d160806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12446 (p : Pattern) (guard : d160807 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d160796 p = 1 := by simpa only [d160807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12435 p hg
    simpa only [d160807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160806 p = 1 := by simpa only [d160807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12445 p hg
    simpa only [d160807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12447 (p : Pattern) (guard : d160808 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d160797 p = 1 := by simpa only [d160808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12436 p hg
    simpa only [d160808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160807 p = 1 := by simpa only [d160808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12446 p hg
    simpa only [d160808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12448 (p : Pattern) (guard : d160809 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160808 p = 1 := by simpa only [d160809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12447 p hg
    simpa only [d160809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12449 (p : Pattern) (guard : d160810 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 51 with
  | false =>
    have hg : d160799 p = 1 := by simpa only [d160810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12438 p hg
    simpa only [d160810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160809 p = 1 := by simpa only [d160810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12448 p hg
    simpa only [d160810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12450 (p : Pattern) (guard : d160811 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160785 p = 1 := by simpa only [d160811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12424 p hg
    simpa only [d160811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12451 (p : Pattern) (guard : d160812 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160811 p = 1 := by simpa only [d160812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12450 p hg
    simpa only [d160812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12452 (p : Pattern) (guard : d160813 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160789 p = 1 := by simpa only [d160813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12428 p hg
    simpa only [d160813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12453 (p : Pattern) (guard : d160814 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160813 p = 1 := by simpa only [d160814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12452 p hg
    simpa only [d160814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12454 (p : Pattern) (guard : d160815 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160812 p = 1 := by simpa only [d160815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12451 p hg
    simpa only [d160815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160814 p = 1 := by simpa only [d160815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12453 p hg
    simpa only [d160815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12455 (p : Pattern) (guard : d160816 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160815 p = 1 := by simpa only [d160816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12454 p hg
    simpa only [d160816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12456 (p : Pattern) (guard : d160817 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160816 p = 1 := by simpa only [d160817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12455 p hg
    simpa only [d160817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12457 (p : Pattern) (guard : d160818 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160817 p = 1 := by simpa only [d160818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12456 p hg
    simpa only [d160818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12458 (p : Pattern) (guard : d160819 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160784 p = 1 := by simpa only [d160819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12423 p hg
    simpa only [d160819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12459 (p : Pattern) (guard : d160820 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160819 p = 1 := by simpa only [d160820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12458 p hg
    simpa only [d160820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12460 (p : Pattern) (guard : d160821 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160820 p = 1 := by simpa only [d160821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12459 p hg
    simpa only [d160821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12461 (p : Pattern) (guard : d160822 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160788 p = 1 := by simpa only [d160822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12427 p hg
    simpa only [d160822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12462 (p : Pattern) (guard : d160823 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160822 p = 1 := by simpa only [d160823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12461 p hg
    simpa only [d160823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12463 (p : Pattern) (guard : d160824 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160823 p = 1 := by simpa only [d160824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12462 p hg
    simpa only [d160824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12464 (p : Pattern) (guard : d160825 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160821 p = 1 := by simpa only [d160825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12460 p hg
    simpa only [d160825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160824 p = 1 := by simpa only [d160825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12463 p hg
    simpa only [d160825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12465 (p : Pattern) (guard : d160826 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160825 p = 1 := by simpa only [d160826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12464 p hg
    simpa only [d160826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12466 (p : Pattern) (guard : d160827 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160826 p = 1 := by simpa only [d160827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12465 p hg
    simpa only [d160827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12467 (p : Pattern) (guard : d2037 p = 1) : d47664 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2037, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10994 p hg
    simpa only [d2037, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2036 p = 1 := by simpa only [d2037, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7208 p hg
    simpa only [d2037, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12468 (p : Pattern) (guard : d2038 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2037 p = 1 := by simpa only [d2038, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12467 p hg
    simpa only [d2038, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2038, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10996 p hg
    simpa only [d2038, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12469 (p : Pattern) (guard : d160828 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2038 p = 1 := by simpa only [d160828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12468 p hg
    simpa only [d160828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12470 (p : Pattern) (guard : d160829 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160828 p = 1 := by simpa only [d160829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12469 p hg
    simpa only [d160829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12471 (p : Pattern) (guard : d160830 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160829 p = 1 := by simpa only [d160830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12470 p hg
    simpa only [d160830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160765 p = 1 := by simpa only [d160830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12402 p hg
    simpa only [d160830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12472 (p : Pattern) (guard : d160831 p = 1) : d47686 p ≤ (-1 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160831, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10992 p hg
    simpa only [d160831, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160830 p = 1 := by simpa only [d160831, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12471 p hg
    simpa only [d160831, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12473 (p : Pattern) (guard : d160832 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160832, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10991 p hg
    simpa only [d160832, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160831 p = 1 := by simpa only [d160832, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12472 p hg
    simpa only [d160832, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12474 (p : Pattern) (guard : d5715 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7197 p hg
    simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12475 (p : Pattern) (guard : d5716 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5715 p = 1 := by simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12474 p hg
    simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12476 (p : Pattern) (guard : d5717 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5716 p = 1 := by simpa only [d5717, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12475 p hg
    simpa only [d5717, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5717, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d5717, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12477 (p : Pattern) (guard : d13677 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5717 p = 1 := by simpa only [d13677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12476 p hg
    simpa only [d13677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4418 p hg
    simpa only [d13677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12478 (p : Pattern) (guard : d13678 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d13677 p = 1 := by simpa only [d13678, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12477 p hg
    simpa only [d13678, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13678, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d13678, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12479 (p : Pattern) (guard : d13679 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d13678 p = 1 := by simpa only [d13679, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12478 p hg
    simpa only [d13679, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13679, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d13679, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12480 (p : Pattern) (guard : d13680 p = 1) : d47664 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d13680, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10994 p hg
    simpa only [d13680, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13679 p = 1 := by simpa only [d13680, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12479 p hg
    simpa only [d13680, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12481 (p : Pattern) (guard : d13681 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13680 p = 1 := by simpa only [d13681, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12480 p hg
    simpa only [d13681, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13681, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10996 p hg
    simpa only [d13681, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12482 (p : Pattern) (guard : d160833 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13681 p = 1 := by simpa only [d160833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12481 p hg
    simpa only [d160833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12483 (p : Pattern) (guard : d160834 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160833 p = 1 := by simpa only [d160834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12482 p hg
    simpa only [d160834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12484 (p : Pattern) (guard : d160835 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160765 p = 1 := by simpa only [d160835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12402 p hg
    simpa only [d160835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160834 p = 1 := by simpa only [d160835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12483 p hg
    simpa only [d160835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12485 (p : Pattern) (guard : d160836 p = 1) : d47686 p ≤ (-1 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160836, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10992 p hg
    simpa only [d160836, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160835 p = 1 := by simpa only [d160836, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12484 p hg
    simpa only [d160836, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12486 (p : Pattern) (guard : d160837 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160837, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10991 p hg
    simpa only [d160837, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160836 p = 1 := by simpa only [d160837, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12485 p hg
    simpa only [d160837, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12487 (p : Pattern) (guard : d160838 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160832 p = 1 := by simpa only [d160838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12473 p hg
    simpa only [d160838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160837 p = 1 := by simpa only [d160838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12486 p hg
    simpa only [d160838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12488 (p : Pattern) (guard : d160839 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160838 p = 1 := by simpa only [d160839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12487 p hg
    simpa only [d160839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160774 p = 1 := by simpa only [d160839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12413 p hg
    simpa only [d160839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12489 (p : Pattern) (guard : d160840 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160839 p = 1 := by simpa only [d160840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12488 p hg
    simpa only [d160840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d160840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12490 (p : Pattern) (guard : d160841 p = 1) : d47699 p ≤ (-1 : Int) + d159769 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160840 p = 1 := by simpa only [d160841, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12489 p hg
    simpa only [d160841, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160841, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11007 p hg
    simpa only [d160841, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12491 (p : Pattern) (guard : d160842 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160842, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160842, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160841 p = 1 := by simpa only [d160842, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12490 p hg
    simpa only [d160842, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12492 (p : Pattern) (guard : d160843 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160842 p = 1 := by simpa only [d160843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12491 p hg
    simpa only [d160843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160779 p = 1 := by simpa only [d160843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12418 p hg
    simpa only [d160843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12493 (p : Pattern) (guard : d160844 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160843 p = 1 := by simpa only [d160844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12492 p hg
    simpa only [d160844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12494 (p : Pattern) (guard : d160845 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160844 p = 1 := by simpa only [d160845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12493 p hg
    simpa only [d160845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12495 (p : Pattern) (guard : d160846 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160845 p = 1 := by simpa only [d160846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12494 p hg
    simpa only [d160846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12496 (p : Pattern) (guard : d160847 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160846 p = 1 := by simpa only [d160847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12495 p hg
    simpa only [d160847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160787 p = 1 := by simpa only [d160847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12426 p hg
    simpa only [d160847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12497 (p : Pattern) (guard : d160848 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160847 p = 1 := by simpa only [d160848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12496 p hg
    simpa only [d160848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12498 (p : Pattern) (guard : d160849 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160779 p = 1 := by simpa only [d160849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12418 p hg
    simpa only [d160849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12499 (p : Pattern) (guard : d160850 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160849 p = 1 := by simpa only [d160850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12498 p hg
    simpa only [d160850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160850, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
