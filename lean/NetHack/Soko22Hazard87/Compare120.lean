import NetHack.Soko22Hazard87.Compare119
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare30000 (p : Pattern) (guard : d259409 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259408 p = 1 := by simpa only [d259409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29999 p hg
    simpa only [d259409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30001 (p : Pattern) (guard : d259410 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259335 p = 1 := by simpa only [d259410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29919 p hg
    simpa only [d259410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30002 (p : Pattern) (guard : d259411 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259410 p = 1 := by simpa only [d259411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30001 p hg
    simpa only [d259411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30003 (p : Pattern) (guard : d259412 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259411 p = 1 := by simpa only [d259412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30002 p hg
    simpa only [d259412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30004 (p : Pattern) (guard : d259413 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259412 p = 1 := by simpa only [d259413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30003 p hg
    simpa only [d259413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30005 (p : Pattern) (guard : d259414 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259413 p = 1 := by simpa only [d259414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30004 p hg
    simpa only [d259414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30006 (p : Pattern) (guard : d259415 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259414 p = 1 := by simpa only [d259415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30005 p hg
    simpa only [d259415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30007 (p : Pattern) (guard : d259416 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259409 p = 1 := by simpa only [d259416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30000 p hg
    simpa only [d259416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259415 p = 1 := by simpa only [d259416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30006 p hg
    simpa only [d259416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30008 (p : Pattern) (guard : d259417 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d259383 p = 1 := by simpa only [d259417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29967 p hg
    simpa only [d259417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259416 p = 1 := by simpa only [d259417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30007 p hg
    simpa only [d259417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30009 (p : Pattern) (guard : d259418 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d259374 p = 1 := by simpa only [d259418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29958 p hg
    simpa only [d259418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259417 p = 1 := by simpa only [d259418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30008 p hg
    simpa only [d259418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30010 (p : Pattern) (guard : d259419 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259418 p = 1 := by simpa only [d259419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30009 p hg
    simpa only [d259419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30011 (p : Pattern) (guard : d259420 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259367 p = 1 := by simpa only [d259420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29951 p hg
    simpa only [d259420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30012 (p : Pattern) (guard : d259421 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259369 p = 1 := by simpa only [d259421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29953 p hg
    simpa only [d259421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30013 (p : Pattern) (guard : d259422 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259420 p = 1 := by simpa only [d259422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30011 p hg
    simpa only [d259422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259421 p = 1 := by simpa only [d259422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30012 p hg
    simpa only [d259422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30014 (p : Pattern) (guard : d259423 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259422 p = 1 := by simpa only [d259423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30013 p hg
    simpa only [d259423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30015 (p : Pattern) (guard : d259424 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259423 p = 1 := by simpa only [d259424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30014 p hg
    simpa only [d259424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30016 (p : Pattern) (guard : d259425 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259424 p = 1 := by simpa only [d259425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30015 p hg
    simpa only [d259425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30017 (p : Pattern) (guard : d259426 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259376 p = 1 := by simpa only [d259426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29960 p hg
    simpa only [d259426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30018 (p : Pattern) (guard : d259427 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259379 p = 1 := by simpa only [d259427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29963 p hg
    simpa only [d259427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30019 (p : Pattern) (guard : d259428 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259426 p = 1 := by simpa only [d259428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30017 p hg
    simpa only [d259428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259427 p = 1 := by simpa only [d259428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30018 p hg
    simpa only [d259428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30020 (p : Pattern) (guard : d259429 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259428 p = 1 := by simpa only [d259429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30019 p hg
    simpa only [d259429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30021 (p : Pattern) (guard : d259430 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259429 p = 1 := by simpa only [d259430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30020 p hg
    simpa only [d259430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30022 (p : Pattern) (guard : d259431 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259406 p = 1 := by simpa only [d259431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29997 p hg
    simpa only [d259431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30023 (p : Pattern) (guard : d259432 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259431 p = 1 := by simpa only [d259432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30022 p hg
    simpa only [d259432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259356 p = 1 := by simpa only [d259432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29940 p hg
    simpa only [d259432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30024 (p : Pattern) (guard : d259433 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259432 p = 1 := by simpa only [d259433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30023 p hg
    simpa only [d259433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30025 (p : Pattern) (guard : d259434 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259412 p = 1 := by simpa only [d259434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30003 p hg
    simpa only [d259434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30026 (p : Pattern) (guard : d259435 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259434 p = 1 := by simpa only [d259435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30025 p hg
    simpa only [d259435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30027 (p : Pattern) (guard : d259436 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259435 p = 1 := by simpa only [d259436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30026 p hg
    simpa only [d259436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30028 (p : Pattern) (guard : d259437 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259433 p = 1 := by simpa only [d259437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30024 p hg
    simpa only [d259437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259436 p = 1 := by simpa only [d259437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30027 p hg
    simpa only [d259437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30029 (p : Pattern) (guard : d259438 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d259430 p = 1 := by simpa only [d259438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30021 p hg
    simpa only [d259438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259437 p = 1 := by simpa only [d259438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30028 p hg
    simpa only [d259438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30030 (p : Pattern) (guard : d259439 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d259425 p = 1 := by simpa only [d259439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30016 p hg
    simpa only [d259439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259438 p = 1 := by simpa only [d259439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30029 p hg
    simpa only [d259439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30031 (p : Pattern) (guard : d259440 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d259418 p = 1 := by simpa only [d259440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30009 p hg
    simpa only [d259440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259439 p = 1 := by simpa only [d259440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30030 p hg
    simpa only [d259440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30032 (p : Pattern) (guard : d259441 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d259419 p = 1 := by simpa only [d259441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30010 p hg
    simpa only [d259441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259440 p = 1 := by simpa only [d259441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30031 p hg
    simpa only [d259441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30033 (p : Pattern) (guard : d259442 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259347 p = 1 := by simpa only [d259442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29931 p hg
    simpa only [d259442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30034 (p : Pattern) (guard : d259443 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259442 p = 1 := by simpa only [d259443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30033 p hg
    simpa only [d259443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30035 (p : Pattern) (guard : d259444 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259443 p = 1 := by simpa only [d259444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30034 p hg
    simpa only [d259444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30036 (p : Pattern) (guard : d259445 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259444 p = 1 := by simpa only [d259445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30035 p hg
    simpa only [d259445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30037 (p : Pattern) (guard : d259446 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259445 p = 1 := by simpa only [d259446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30036 p hg
    simpa only [d259446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30038 (p : Pattern) (guard : d259447 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d259352 p = 1 := by simpa only [d259447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29936 p hg
    simpa only [d259447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259446 p = 1 := by simpa only [d259447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30037 p hg
    simpa only [d259447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30039 (p : Pattern) (guard : d259448 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259357 p = 1 := by simpa only [d259448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29941 p hg
    simpa only [d259448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30040 (p : Pattern) (guard : d259449 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259448 p = 1 := by simpa only [d259449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30039 p hg
    simpa only [d259449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30041 (p : Pattern) (guard : d259450 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259449 p = 1 := by simpa only [d259450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30040 p hg
    simpa only [d259450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30042 (p : Pattern) (guard : d259451 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259450 p = 1 := by simpa only [d259451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30041 p hg
    simpa only [d259451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30043 (p : Pattern) (guard : d259452 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259451 p = 1 := by simpa only [d259452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30042 p hg
    simpa only [d259452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30044 (p : Pattern) (guard : d259453 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d259446 p = 1 := by simpa only [d259453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30037 p hg
    simpa only [d259453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259452 p = 1 := by simpa only [d259453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30043 p hg
    simpa only [d259453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30045 (p : Pattern) (guard : d259454 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d259447 p = 1 := by simpa only [d259454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30038 p hg
    simpa only [d259454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259453 p = 1 := by simpa only [d259454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30044 p hg
    simpa only [d259454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30046 (p : Pattern) (guard : d259455 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 69 with
  | false =>
    have hg : d259441 p = 1 := by simpa only [d259455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30032 p hg
    simpa only [d259455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259454 p = 1 := by simpa only [d259455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30045 p hg
    simpa only [d259455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30047 (p : Pattern) (guard : d259456 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 51 with
  | false =>
    have hg : d259455 p = 1 := by simpa only [d259456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30046 p hg
    simpa only [d259456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30048 (p : Pattern) (guard : d259457 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 50 with
  | false =>
    have hg : d259366 p = 1 := by simpa only [d259457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29950 p hg
    simpa only [d259457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259456 p = 1 := by simpa only [d259457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30047 p hg
    simpa only [d259457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30049 (p : Pattern) (guard : d258183 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257870 p = 1 := by simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29671 p hg
    simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30050 (p : Pattern) (guard : d258184 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258183 p = 1 := by simpa only [d258184, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30049 p hg
    simpa only [d258184, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258184, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28974 p hg
    simpa only [d258184, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30051 (p : Pattern) (guard : d258185 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28976 p hg
    simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258184 p = 1 := by simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30050 p hg
    simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30052 (p : Pattern) (guard : d258186 p = 1) : d47735 p ≤ (-1 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258185 p = 1 := by simpa only [d258186, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30051 p hg
    simpa only [d258186, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258186, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d258186, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30053 (p : Pattern) (guard : d258187 p = 1) : d47736 p ≤ (-1 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258186 p = 1 := by simpa only [d258187, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30052 p hg
    simpa only [d258187, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258187, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d258187, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30054 (p : Pattern) (guard : d258188 p = 1) : d47737 p ≤ (-1 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258188, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28961 p hg
    simpa only [d258188, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258187 p = 1 := by simpa only [d258188, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30053 p hg
    simpa only [d258188, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30055 (p : Pattern) (guard : d258189 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258188 p = 1 := by simpa only [d258189, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30054 p hg
    simpa only [d258189, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258189, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28982 p hg
    simpa only [d258189, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30056 (p : Pattern) (guard : d259291 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257874 p = 1 := by simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29677 p hg
    simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30057 (p : Pattern) (guard : d259292 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259291 p = 1 := by simpa only [d259292, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30056 p hg
    simpa only [d259292, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259292, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28974 p hg
    simpa only [d259292, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30058 (p : Pattern) (guard : d259293 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d257876 p = 1 := by simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29679 p hg
    simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259292 p = 1 := by simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30057 p hg
    simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30059 (p : Pattern) (guard : d259294 p = 1) : d47735 p ≤ (-1 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259293 p = 1 := by simpa only [d259294, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30058 p hg
    simpa only [d259294, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259294, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d259294, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30060 (p : Pattern) (guard : d259295 p = 1) : d47736 p ≤ (-1 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259294 p = 1 := by simpa only [d259295, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30059 p hg
    simpa only [d259295, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259295, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259295, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30061 (p : Pattern) (guard : d259296 p = 1) : d47737 p ≤ (-1 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259296, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28961 p hg
    simpa only [d259296, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259295 p = 1 := by simpa only [d259296, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30060 p hg
    simpa only [d259296, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30062 (p : Pattern) (guard : d259297 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259296 p = 1 := by simpa only [d259297, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30061 p hg
    simpa only [d259297, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259297, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28982 p hg
    simpa only [d259297, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30063 (p : Pattern) (guard : d259384 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258189 p = 1 := by simpa only [d259384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30055 p hg
    simpa only [d259384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259297 p = 1 := by simpa only [d259384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30062 p hg
    simpa only [d259384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30064 (p : Pattern) (guard : d259385 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258184 p = 1 := by simpa only [d259385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30050 p hg
    simpa only [d259385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259292 p = 1 := by simpa only [d259385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30057 p hg
    simpa only [d259385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30065 (p : Pattern) (guard : d259386 p = 1) : d47735 p ≤ (-1 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259385 p = 1 := by simpa only [d259386, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30064 p hg
    simpa only [d259386, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259386, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d259386, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30066 (p : Pattern) (guard : d259387 p = 1) : d47736 p ≤ (-1 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259386 p = 1 := by simpa only [d259387, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30065 p hg
    simpa only [d259387, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259387, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259387, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30067 (p : Pattern) (guard : d259388 p = 1) : d47737 p ≤ (-1 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259388, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28961 p hg
    simpa only [d259388, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259387 p = 1 := by simpa only [d259388, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30066 p hg
    simpa only [d259388, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30068 (p : Pattern) (guard : d259389 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259388 p = 1 := by simpa only [d259389, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30067 p hg
    simpa only [d259389, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259389, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28982 p hg
    simpa only [d259389, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30069 (p : Pattern) (guard : d2027 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29672 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30070 (p : Pattern) (guard : d2028 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30069 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30071 (p : Pattern) (guard : d2029 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30070 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30072 (p : Pattern) (guard : d2030 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30071 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30073 (p : Pattern) (guard : d27032 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30072 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30074 (p : Pattern) (guard : d259300 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 201 with
  | false =>
    have hg : d27032 p = 1 := by simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30073 p hg
    simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30075 (p : Pattern) (guard : d259301 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259300 p = 1 := by simpa only [d259301, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30074 p hg
    simpa only [d259301, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259301, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28974 p hg
    simpa only [d259301, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30076 (p : Pattern) (guard : d259308 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259292 p = 1 := by simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30057 p hg
    simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259301 p = 1 := by simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30075 p hg
    simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30077 (p : Pattern) (guard : d259309 p = 1) : d47735 p ≤ (-1 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259308 p = 1 := by simpa only [d259309, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30076 p hg
    simpa only [d259309, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259309, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d259309, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30078 (p : Pattern) (guard : d259310 p = 1) : d47736 p ≤ (-1 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259309 p = 1 := by simpa only [d259310, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30077 p hg
    simpa only [d259310, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259310, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259310, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30079 (p : Pattern) (guard : d259311 p = 1) : d47737 p ≤ (-1 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259311, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28961 p hg
    simpa only [d259311, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259310 p = 1 := by simpa only [d259311, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30078 p hg
    simpa only [d259311, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30080 (p : Pattern) (guard : d259312 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259311 p = 1 := by simpa only [d259312, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30079 p hg
    simpa only [d259312, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259312, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28982 p hg
    simpa only [d259312, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30081 (p : Pattern) (guard : d259390 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259389 p = 1 := by simpa only [d259390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30068 p hg
    simpa only [d259390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259312 p = 1 := by simpa only [d259390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30080 p hg
    simpa only [d259390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30082 (p : Pattern) (guard : d259391 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259384 p = 1 := by simpa only [d259391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30063 p hg
    simpa only [d259391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259390 p = 1 := by simpa only [d259391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30081 p hg
    simpa only [d259391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30083 (p : Pattern) (guard : d259298 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257874 p = 1 := by simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29677 p hg
    simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d27032 p = 1 := by simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30073 p hg
    simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30084 (p : Pattern) (guard : d259299 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259298 p = 1 := by simpa only [d259299, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30083 p hg
    simpa only [d259299, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259299, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28974 p hg
    simpa only [d259299, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30085 (p : Pattern) (guard : d259302 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259299 p = 1 := by simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30084 p hg
    simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259301 p = 1 := by simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30075 p hg
    simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30086 (p : Pattern) (guard : d259303 p = 1) : d47735 p ≤ (-1 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259302 p = 1 := by simpa only [d259303, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30085 p hg
    simpa only [d259303, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259303, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d259303, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30087 (p : Pattern) (guard : d259304 p = 1) : d47736 p ≤ (-1 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259303 p = 1 := by simpa only [d259304, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30086 p hg
    simpa only [d259304, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259304, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259304, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30088 (p : Pattern) (guard : d259305 p = 1) : d47737 p ≤ (-1 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259305, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28961 p hg
    simpa only [d259305, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259304 p = 1 := by simpa only [d259305, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30087 p hg
    simpa only [d259305, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30089 (p : Pattern) (guard : d259306 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259305 p = 1 := by simpa only [d259306, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30088 p hg
    simpa only [d259306, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259306, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28982 p hg
    simpa only [d259306, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30090 (p : Pattern) (guard : d259307 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259297 p = 1 := by simpa only [d259307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30062 p hg
    simpa only [d259307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259306 p = 1 := by simpa only [d259307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30089 p hg
    simpa only [d259307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30091 (p : Pattern) (guard : d259313 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259301 p = 1 := by simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30075 p hg
    simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28976 p hg
    simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30092 (p : Pattern) (guard : d259314 p = 1) : d47735 p ≤ (-1 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259313 p = 1 := by simpa only [d259314, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30091 p hg
    simpa only [d259314, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259314, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d259314, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30093 (p : Pattern) (guard : d259315 p = 1) : d47736 p ≤ (-1 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259314 p = 1 := by simpa only [d259315, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30092 p hg
    simpa only [d259315, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259315, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259315, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30094 (p : Pattern) (guard : d259316 p = 1) : d47737 p ≤ (-1 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259316, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28961 p hg
    simpa only [d259316, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259315 p = 1 := by simpa only [d259316, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30093 p hg
    simpa only [d259316, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30095 (p : Pattern) (guard : d259317 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259316 p = 1 := by simpa only [d259317, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30094 p hg
    simpa only [d259317, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259317, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28982 p hg
    simpa only [d259317, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30096 (p : Pattern) (guard : d259318 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259312 p = 1 := by simpa only [d259318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30080 p hg
    simpa only [d259318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259317 p = 1 := by simpa only [d259318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30095 p hg
    simpa only [d259318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30097 (p : Pattern) (guard : d259319 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259307 p = 1 := by simpa only [d259319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30090 p hg
    simpa only [d259319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259318 p = 1 := by simpa only [d259319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30096 p hg
    simpa only [d259319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30098 (p : Pattern) (guard : d259392 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259391 p = 1 := by simpa only [d259392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30082 p hg
    simpa only [d259392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259319 p = 1 := by simpa only [d259392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30097 p hg
    simpa only [d259392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30099 (p : Pattern) (guard : d259393 p = 1) : d47756 p ≤ (-1 : Int) + d253395 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259393, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28960 p hg
    simpa only [d259393, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259392 p = 1 := by simpa only [d259393, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30098 p hg
    simpa only [d259393, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30100 (p : Pattern) (guard : d259394 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259394, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28959 p hg
    simpa only [d259394, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259393 p = 1 := by simpa only [d259394, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30099 p hg
    simpa only [d259394, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30101 (p : Pattern) (guard : d259321 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259317 p = 1 := by simpa only [d259321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30095 p hg
    simpa only [d259321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28984 p hg
    simpa only [d259321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30102 (p : Pattern) (guard : d259395 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259318 p = 1 := by simpa only [d259395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30096 p hg
    simpa only [d259395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259321 p = 1 := by simpa only [d259395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30101 p hg
    simpa only [d259395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30103 (p : Pattern) (guard : d259396 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259319 p = 1 := by simpa only [d259396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30097 p hg
    simpa only [d259396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259395 p = 1 := by simpa only [d259396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30102 p hg
    simpa only [d259396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30104 (p : Pattern) (guard : d259397 p = 1) : d47756 p ≤ (-1 : Int) + d253395 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259397, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28960 p hg
    simpa only [d259397, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259396 p = 1 := by simpa only [d259397, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30103 p hg
    simpa only [d259397, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30105 (p : Pattern) (guard : d259398 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259398, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28959 p hg
    simpa only [d259398, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259397 p = 1 := by simpa only [d259398, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30104 p hg
    simpa only [d259398, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30106 (p : Pattern) (guard : d259399 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259394 p = 1 := by simpa only [d259399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30100 p hg
    simpa only [d259399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259398 p = 1 := by simpa only [d259399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30105 p hg
    simpa only [d259399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30107 (p : Pattern) (guard : d259320 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259306 p = 1 := by simpa only [d259320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30089 p hg
    simpa only [d259320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259317 p = 1 := by simpa only [d259320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30095 p hg
    simpa only [d259320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30108 (p : Pattern) (guard : d259322 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259320 p = 1 := by simpa only [d259322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30107 p hg
    simpa only [d259322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259321 p = 1 := by simpa only [d259322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30101 p hg
    simpa only [d259322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30109 (p : Pattern) (guard : d259323 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259319 p = 1 := by simpa only [d259323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30097 p hg
    simpa only [d259323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259322 p = 1 := by simpa only [d259323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30108 p hg
    simpa only [d259323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30110 (p : Pattern) (guard : d259324 p = 1) : d47756 p ≤ (-1 : Int) + d253395 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259324, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28960 p hg
    simpa only [d259324, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259323 p = 1 := by simpa only [d259324, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30109 p hg
    simpa only [d259324, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30111 (p : Pattern) (guard : d259325 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259325, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28959 p hg
    simpa only [d259325, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259324 p = 1 := by simpa only [d259325, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30110 p hg
    simpa only [d259325, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30112 (p : Pattern) (guard : d259326 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259321 p = 1 := by simpa only [d259326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30101 p hg
    simpa only [d259326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28984 p hg
    simpa only [d259326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30113 (p : Pattern) (guard : d259327 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259322 p = 1 := by simpa only [d259327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30108 p hg
    simpa only [d259327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259326 p = 1 := by simpa only [d259327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30112 p hg
    simpa only [d259327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30114 (p : Pattern) (guard : d259328 p = 1) : d47756 p ≤ (-1 : Int) + d253395 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259328, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28960 p hg
    simpa only [d259328, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259327 p = 1 := by simpa only [d259328, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30113 p hg
    simpa only [d259328, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30115 (p : Pattern) (guard : d259329 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259329, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28959 p hg
    simpa only [d259329, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259328 p = 1 := by simpa only [d259329, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30114 p hg
    simpa only [d259329, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30116 (p : Pattern) (guard : d259330 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259325 p = 1 := by simpa only [d259330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30111 p hg
    simpa only [d259330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259329 p = 1 := by simpa only [d259330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30115 p hg
    simpa only [d259330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30117 (p : Pattern) (guard : d259400 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259399 p = 1 := by simpa only [d259400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30106 p hg
    simpa only [d259400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259330 p = 1 := by simpa only [d259400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30116 p hg
    simpa only [d259400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30118 (p : Pattern) (guard : d259401 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259400 p = 1 := by simpa only [d259401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30117 p hg
    simpa only [d259401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28990 p hg
    simpa only [d259401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30119 (p : Pattern) (guard : d259402 p = 1) : d47765 p ≤ (-1 : Int) + d253404 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259401 p = 1 := by simpa only [d259402, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30118 p hg
    simpa only [d259402, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259402, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28994 p hg
    simpa only [d259402, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30120 (p : Pattern) (guard : d259403 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259403, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28958 p hg
    simpa only [d259403, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259402 p = 1 := by simpa only [d259403, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30119 p hg
    simpa only [d259403, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30121 (p : Pattern) (guard : d259331 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259329 p = 1 := by simpa only [d259331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30115 p hg
    simpa only [d259331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28990 p hg
    simpa only [d259331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30122 (p : Pattern) (guard : d259332 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259330 p = 1 := by simpa only [d259332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30116 p hg
    simpa only [d259332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259331 p = 1 := by simpa only [d259332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30121 p hg
    simpa only [d259332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30123 (p : Pattern) (guard : d259333 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259332 p = 1 := by simpa only [d259333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30122 p hg
    simpa only [d259333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28990 p hg
    simpa only [d259333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30124 (p : Pattern) (guard : d259334 p = 1) : d47765 p ≤ (-1 : Int) + d253404 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259333 p = 1 := by simpa only [d259334, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30123 p hg
    simpa only [d259334, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259334, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28994 p hg
    simpa only [d259334, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30125 (p : Pattern) (guard : d259335 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259335, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28958 p hg
    simpa only [d259335, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259334 p = 1 := by simpa only [d259335, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30124 p hg
    simpa only [d259335, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30126 (p : Pattern) (guard : d259404 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259403 p = 1 := by simpa only [d259404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30120 p hg
    simpa only [d259404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259335 p = 1 := by simpa only [d259404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30125 p hg
    simpa only [d259404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30127 (p : Pattern) (guard : d259405 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259404 p = 1 := by simpa only [d259405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30126 p hg
    simpa only [d259405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30128 (p : Pattern) (guard : d259406 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259405 p = 1 := by simpa only [d259406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30127 p hg
    simpa only [d259406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30129 (p : Pattern) (guard : d259431 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259406 p = 1 := by simpa only [d259431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30128 p hg
    simpa only [d259431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30130 (p : Pattern) (guard : d259336 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259331 p = 1 := by simpa only [d259336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30121 p hg
    simpa only [d259336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28990 p hg
    simpa only [d259336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30131 (p : Pattern) (guard : d259337 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259336 p = 1 := by simpa only [d259337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30130 p hg
    simpa only [d259337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28990 p hg
    simpa only [d259337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30132 (p : Pattern) (guard : d259338 p = 1) : d47765 p ≤ (-1 : Int) + d253404 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259337 p = 1 := by simpa only [d259338, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30131 p hg
    simpa only [d259338, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259338, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28994 p hg
    simpa only [d259338, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30133 (p : Pattern) (guard : d259339 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259339, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28958 p hg
    simpa only [d259339, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259338 p = 1 := by simpa only [d259339, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30132 p hg
    simpa only [d259339, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30134 (p : Pattern) (guard : d259340 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259335 p = 1 := by simpa only [d259340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30125 p hg
    simpa only [d259340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259339 p = 1 := by simpa only [d259340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30133 p hg
    simpa only [d259340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30135 (p : Pattern) (guard : d259341 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259340 p = 1 := by simpa only [d259341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30134 p hg
    simpa only [d259341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30136 (p : Pattern) (guard : d259342 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259341 p = 1 := by simpa only [d259342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30135 p hg
    simpa only [d259342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30137 (p : Pattern) (guard : d259356 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259342 p = 1 := by simpa only [d259356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30136 p hg
    simpa only [d259356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30138 (p : Pattern) (guard : d259432 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259431 p = 1 := by simpa only [d259432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30129 p hg
    simpa only [d259432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259356 p = 1 := by simpa only [d259432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30137 p hg
    simpa only [d259432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30139 (p : Pattern) (guard : d259433 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259432 p = 1 := by simpa only [d259433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30138 p hg
    simpa only [d259433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30140 (p : Pattern) (guard : d259410 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259335 p = 1 := by simpa only [d259410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30125 p hg
    simpa only [d259410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30141 (p : Pattern) (guard : d259411 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259410 p = 1 := by simpa only [d259411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30140 p hg
    simpa only [d259411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30142 (p : Pattern) (guard : d259412 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259411 p = 1 := by simpa only [d259412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30141 p hg
    simpa only [d259412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30143 (p : Pattern) (guard : d259434 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259412 p = 1 := by simpa only [d259434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30142 p hg
    simpa only [d259434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30144 (p : Pattern) (guard : d259435 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259434 p = 1 := by simpa only [d259435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30143 p hg
    simpa only [d259435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30145 (p : Pattern) (guard : d259436 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259435 p = 1 := by simpa only [d259436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30144 p hg
    simpa only [d259436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30146 (p : Pattern) (guard : d259437 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259433 p = 1 := by simpa only [d259437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30139 p hg
    simpa only [d259437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259436 p = 1 := by simpa only [d259437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30145 p hg
    simpa only [d259437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30147 (p : Pattern) (guard : d259458 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259437 p = 1 := by simpa only [d259458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30146 p hg
    simpa only [d259458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30148 (p : Pattern) (guard : d259459 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259458 p = 1 := by simpa only [d259459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30147 p hg
    simpa only [d259459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30149 (p : Pattern) (guard : d259460 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259460, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259460, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259459 p = 1 := by simpa only [d259460, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30148 p hg
    simpa only [d259460, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30150 (p : Pattern) (guard : d259461 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d259461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259460 p = 1 := by simpa only [d259461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30149 p hg
    simpa only [d259461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30151 (p : Pattern) (guard : d259344 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259339 p = 1 := by simpa only [d259344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30133 p hg
    simpa only [d259344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30152 (p : Pattern) (guard : d259345 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259344 p = 1 := by simpa only [d259345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30151 p hg
    simpa only [d259345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30153 (p : Pattern) (guard : d259346 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259345 p = 1 := by simpa only [d259346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30152 p hg
    simpa only [d259346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30154 (p : Pattern) (guard : d259357 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259346 p = 1 := by simpa only [d259357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30153 p hg
    simpa only [d259357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30155 (p : Pattern) (guard : d259448 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259357 p = 1 := by simpa only [d259448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30154 p hg
    simpa only [d259448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30156 (p : Pattern) (guard : d259449 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259448 p = 1 := by simpa only [d259449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30155 p hg
    simpa only [d259449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30157 (p : Pattern) (guard : d259450 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259449 p = 1 := by simpa only [d259450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30156 p hg
    simpa only [d259450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30158 (p : Pattern) (guard : d259451 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259450 p = 1 := by simpa only [d259451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30157 p hg
    simpa only [d259451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30159 (p : Pattern) (guard : d259452 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d259452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259451 p = 1 := by simpa only [d259452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30158 p hg
    simpa only [d259452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30160 (p : Pattern) (guard : d259462 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259462, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259462, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259452 p = 1 := by simpa only [d259462, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30159 p hg
    simpa only [d259462, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30161 (p : Pattern) (guard : d259463 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d259463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259462 p = 1 := by simpa only [d259463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30160 p hg
    simpa only [d259463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30162 (p : Pattern) (guard : d259464 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 69 with
  | false =>
    have hg : d259461 p = 1 := by simpa only [d259464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30150 p hg
    simpa only [d259464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259463 p = 1 := by simpa only [d259464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30161 p hg
    simpa only [d259464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30163 (p : Pattern) (guard : d259465 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 51 with
  | false =>
    have hg : d259464 p = 1 := by simpa only [d259465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30162 p hg
    simpa only [d259465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d259465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30164 (p : Pattern) (guard : d259466 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  cases selected : p 50 with
  | false =>
    have hg : d259465 p = 1 := by simpa only [d259466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30163 p hg
    simpa only [d259466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28956 p hg
    simpa only [d259466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30165 (p : Pattern) (guard : d259467 p = 1) : d47768 p ≤ (-1 : Int) + d253407 p := by
  cases selected : p 49 with
  | false =>
    have hg : d259457 p = 1 := by simpa only [d259467, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30048 p hg
    simpa only [d259467, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259466 p = 1 := by simpa only [d259467, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30164 p hg
    simpa only [d259467, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30166 (p : Pattern) (guard : d258183 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257870 p = 1 := by simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29756 p hg
    simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30167 (p : Pattern) (guard : d258184 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258183 p = 1 := by simpa only [d258184, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30166 p hg
    simpa only [d258184, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258184, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29029 p hg
    simpa only [d258184, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30168 (p : Pattern) (guard : d258185 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29016 p hg
    simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258184 p = 1 := by simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30167 p hg
    simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30169 (p : Pattern) (guard : d258274 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29016 p hg
    simpa only [d258274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258185 p = 1 := by simpa only [d258274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30168 p hg
    simpa only [d258274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30170 (p : Pattern) (guard : d258186 p = 1) : d47797 p ≤ (-1 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258185 p = 1 := by simpa only [d258186, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29970 p hg
    simpa only [d258186, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258186, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d258186, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30171 (p : Pattern) (guard : d258275 p = 1) : d47798 p ≤ (-1 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258274 p = 1 := by simpa only [d258275, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30169 p hg
    simpa only [d258275, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258186 p = 1 := by simpa only [d258275, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30170 p hg
    simpa only [d258275, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30172 (p : Pattern) (guard : d258183 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257870 p = 1 := by simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29775 p hg
    simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30173 (p : Pattern) (guard : d258184 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258183 p = 1 := by simpa only [d258184, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30172 p hg
    simpa only [d258184, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258184, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29047 p hg
    simpa only [d258184, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30174 (p : Pattern) (guard : d258185 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29049 p hg
    simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258184 p = 1 := by simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30173 p hg
    simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30175 (p : Pattern) (guard : d258186 p = 1) : d47682 p ≤ (-1 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258185 p = 1 := by simpa only [d258186, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30174 p hg
    simpa only [d258186, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258186, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d258186, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30176 (p : Pattern) (guard : d258187 p = 1) : d47683 p ≤ (-1 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258186 p = 1 := by simpa only [d258187, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30175 p hg
    simpa only [d258187, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258187, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d258187, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30177 (p : Pattern) (guard : d258276 p = 1) : d47799 p ≤ (-1 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d258275 p = 1 := by simpa only [d258276, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30171 p hg
    simpa only [d258276, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258187 p = 1 := by simpa only [d258276, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30176 p hg
    simpa only [d258276, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30178 (p : Pattern) (guard : d258277 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258276 p = 1 := by simpa only [d258277, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30177 p hg
    simpa only [d258277, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258277, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29054 p hg
    simpa only [d258277, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30179 (p : Pattern) (guard : d259291 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257874 p = 1 := by simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29762 p hg
    simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30180 (p : Pattern) (guard : d259292 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259291 p = 1 := by simpa only [d259292, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30179 p hg
    simpa only [d259292, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259292, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29029 p hg
    simpa only [d259292, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30181 (p : Pattern) (guard : d259293 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d257876 p = 1 := by simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29764 p hg
    simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259292 p = 1 := by simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30180 p hg
    simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30182 (p : Pattern) (guard : d259468 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29016 p hg
    simpa only [d259468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259293 p = 1 := by simpa only [d259468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30181 p hg
    simpa only [d259468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30183 (p : Pattern) (guard : d259294 p = 1) : d47797 p ≤ (-1 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259293 p = 1 := by simpa only [d259294, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29872 p hg
    simpa only [d259294, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259294, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d259294, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30184 (p : Pattern) (guard : d259469 p = 1) : d47798 p ≤ (-1 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259468 p = 1 := by simpa only [d259469, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30182 p hg
    simpa only [d259469, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259294 p = 1 := by simpa only [d259469, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30183 p hg
    simpa only [d259469, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30185 (p : Pattern) (guard : d259291 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257874 p = 1 := by simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29781 p hg
    simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30186 (p : Pattern) (guard : d259292 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259291 p = 1 := by simpa only [d259292, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30185 p hg
    simpa only [d259292, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259292, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29047 p hg
    simpa only [d259292, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30187 (p : Pattern) (guard : d259293 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d257876 p = 1 := by simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29783 p hg
    simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259292 p = 1 := by simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30186 p hg
    simpa only [d259293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30188 (p : Pattern) (guard : d259294 p = 1) : d47682 p ≤ (-1 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259293 p = 1 := by simpa only [d259294, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30187 p hg
    simpa only [d259294, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259294, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259294, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30189 (p : Pattern) (guard : d259295 p = 1) : d47683 p ≤ (-1 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259294 p = 1 := by simpa only [d259295, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30188 p hg
    simpa only [d259295, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259295, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259295, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30190 (p : Pattern) (guard : d259470 p = 1) : d47799 p ≤ (-1 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d259469 p = 1 := by simpa only [d259470, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30184 p hg
    simpa only [d259470, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259295 p = 1 := by simpa only [d259470, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30189 p hg
    simpa only [d259470, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30191 (p : Pattern) (guard : d259471 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259470 p = 1 := by simpa only [d259471, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30190 p hg
    simpa only [d259471, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259471, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29054 p hg
    simpa only [d259471, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30192 (p : Pattern) (guard : d259472 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258277 p = 1 := by simpa only [d259472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30178 p hg
    simpa only [d259472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259471 p = 1 := by simpa only [d259472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30191 p hg
    simpa only [d259472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30193 (p : Pattern) (guard : d259385 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258184 p = 1 := by simpa only [d259385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30167 p hg
    simpa only [d259385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259292 p = 1 := by simpa only [d259385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30180 p hg
    simpa only [d259385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30194 (p : Pattern) (guard : d259473 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29016 p hg
    simpa only [d259473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259385 p = 1 := by simpa only [d259473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30193 p hg
    simpa only [d259473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30195 (p : Pattern) (guard : d259386 p = 1) : d47797 p ≤ (-1 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259385 p = 1 := by simpa only [d259386, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29976 p hg
    simpa only [d259386, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259386, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d259386, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30196 (p : Pattern) (guard : d259474 p = 1) : d47798 p ≤ (-1 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259473 p = 1 := by simpa only [d259474, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30194 p hg
    simpa only [d259474, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259386 p = 1 := by simpa only [d259474, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30195 p hg
    simpa only [d259474, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30197 (p : Pattern) (guard : d259385 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258184 p = 1 := by simpa only [d259385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30173 p hg
    simpa only [d259385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259292 p = 1 := by simpa only [d259385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30186 p hg
    simpa only [d259385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30198 (p : Pattern) (guard : d259386 p = 1) : d47682 p ≤ (-1 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259385 p = 1 := by simpa only [d259386, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30197 p hg
    simpa only [d259386, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259386, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259386, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30199 (p : Pattern) (guard : d259387 p = 1) : d47683 p ≤ (-1 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259386 p = 1 := by simpa only [d259387, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30198 p hg
    simpa only [d259387, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259387, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259387, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30200 (p : Pattern) (guard : d259475 p = 1) : d47799 p ≤ (-1 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d259474 p = 1 := by simpa only [d259475, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30196 p hg
    simpa only [d259475, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259387 p = 1 := by simpa only [d259475, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30199 p hg
    simpa only [d259475, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30201 (p : Pattern) (guard : d259476 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259475 p = 1 := by simpa only [d259476, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30200 p hg
    simpa only [d259476, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259476, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29054 p hg
    simpa only [d259476, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30202 (p : Pattern) (guard : d2027 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29757 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30203 (p : Pattern) (guard : d2028 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30202 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30204 (p : Pattern) (guard : d2029 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30203 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30205 (p : Pattern) (guard : d2030 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30204 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30206 (p : Pattern) (guard : d27032 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30205 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30207 (p : Pattern) (guard : d259300 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 201 with
  | false =>
    have hg : d27032 p = 1 := by simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30206 p hg
    simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29017 p hg
    simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30208 (p : Pattern) (guard : d259301 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259300 p = 1 := by simpa only [d259301, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30207 p hg
    simpa only [d259301, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259301, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29029 p hg
    simpa only [d259301, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30209 (p : Pattern) (guard : d259308 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259292 p = 1 := by simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30180 p hg
    simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259301 p = 1 := by simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30208 p hg
    simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30210 (p : Pattern) (guard : d259477 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29016 p hg
    simpa only [d259477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259308 p = 1 := by simpa only [d259477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30209 p hg
    simpa only [d259477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30211 (p : Pattern) (guard : d259309 p = 1) : d47797 p ≤ (-1 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259308 p = 1 := by simpa only [d259309, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29892 p hg
    simpa only [d259309, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259309, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d259309, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30212 (p : Pattern) (guard : d259478 p = 1) : d47798 p ≤ (-1 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259477 p = 1 := by simpa only [d259478, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30210 p hg
    simpa only [d259478, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259309 p = 1 := by simpa only [d259478, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30211 p hg
    simpa only [d259478, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30213 (p : Pattern) (guard : d2027 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29776 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30214 (p : Pattern) (guard : d2028 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30213 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30215 (p : Pattern) (guard : d2029 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30214 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30216 (p : Pattern) (guard : d2030 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30215 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30217 (p : Pattern) (guard : d27032 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30216 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d27032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30218 (p : Pattern) (guard : d259300 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 201 with
  | false =>
    have hg : d27032 p = 1 := by simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30217 p hg
    simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29035 p hg
    simpa only [d259300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30219 (p : Pattern) (guard : d259301 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259300 p = 1 := by simpa only [d259301, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30218 p hg
    simpa only [d259301, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259301, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29047 p hg
    simpa only [d259301, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30220 (p : Pattern) (guard : d259308 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259292 p = 1 := by simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30186 p hg
    simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259301 p = 1 := by simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30219 p hg
    simpa only [d259308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30221 (p : Pattern) (guard : d259309 p = 1) : d47682 p ≤ (-1 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259308 p = 1 := by simpa only [d259309, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30220 p hg
    simpa only [d259309, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259309, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259309, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30222 (p : Pattern) (guard : d259310 p = 1) : d47683 p ≤ (-1 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259309 p = 1 := by simpa only [d259310, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30221 p hg
    simpa only [d259310, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259310, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259310, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30223 (p : Pattern) (guard : d259479 p = 1) : d47799 p ≤ (-1 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d259478 p = 1 := by simpa only [d259479, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30212 p hg
    simpa only [d259479, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259310 p = 1 := by simpa only [d259479, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30222 p hg
    simpa only [d259479, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30224 (p : Pattern) (guard : d259480 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259479 p = 1 := by simpa only [d259480, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30223 p hg
    simpa only [d259480, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259480, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29054 p hg
    simpa only [d259480, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30225 (p : Pattern) (guard : d259481 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259476 p = 1 := by simpa only [d259481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30201 p hg
    simpa only [d259481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259480 p = 1 := by simpa only [d259481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30224 p hg
    simpa only [d259481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30226 (p : Pattern) (guard : d259482 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259472 p = 1 := by simpa only [d259482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30192 p hg
    simpa only [d259482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259481 p = 1 := by simpa only [d259482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30225 p hg
    simpa only [d259482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30227 (p : Pattern) (guard : d259298 p = 1) : d47630 p ≤ (-1 : Int) + d47629 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257874 p = 1 := by simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29762 p hg
    simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d27032 p = 1 := by simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30206 p hg
    simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30228 (p : Pattern) (guard : d259299 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259298 p = 1 := by simpa only [d259299, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30227 p hg
    simpa only [d259299, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259299, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29029 p hg
    simpa only [d259299, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30229 (p : Pattern) (guard : d259302 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259299 p = 1 := by simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30228 p hg
    simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259301 p = 1 := by simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30208 p hg
    simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30230 (p : Pattern) (guard : d259483 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29016 p hg
    simpa only [d259483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259302 p = 1 := by simpa only [d259483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30229 p hg
    simpa only [d259483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30231 (p : Pattern) (guard : d259303 p = 1) : d47797 p ≤ (-1 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259302 p = 1 := by simpa only [d259303, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29886 p hg
    simpa only [d259303, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259303, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d259303, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30232 (p : Pattern) (guard : d259484 p = 1) : d47798 p ≤ (-1 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259483 p = 1 := by simpa only [d259484, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30230 p hg
    simpa only [d259484, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259303 p = 1 := by simpa only [d259484, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30231 p hg
    simpa only [d259484, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30233 (p : Pattern) (guard : d259298 p = 1) : d47634 p ≤ (-1 : Int) + d47633 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257874 p = 1 := by simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29781 p hg
    simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d27032 p = 1 := by simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30217 p hg
    simpa only [d259298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30234 (p : Pattern) (guard : d259299 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259298 p = 1 := by simpa only [d259299, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30233 p hg
    simpa only [d259299, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259299, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29047 p hg
    simpa only [d259299, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30235 (p : Pattern) (guard : d259302 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259299 p = 1 := by simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30234 p hg
    simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259301 p = 1 := by simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30219 p hg
    simpa only [d259302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30236 (p : Pattern) (guard : d259303 p = 1) : d47682 p ≤ (-1 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259302 p = 1 := by simpa only [d259303, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30235 p hg
    simpa only [d259303, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259303, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259303, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30237 (p : Pattern) (guard : d259304 p = 1) : d47683 p ≤ (-1 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259303 p = 1 := by simpa only [d259304, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30236 p hg
    simpa only [d259304, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259304, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259304, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30238 (p : Pattern) (guard : d259485 p = 1) : d47799 p ≤ (-1 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d259484 p = 1 := by simpa only [d259485, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30232 p hg
    simpa only [d259485, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259304 p = 1 := by simpa only [d259485, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30237 p hg
    simpa only [d259485, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30239 (p : Pattern) (guard : d259486 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259485 p = 1 := by simpa only [d259486, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30238 p hg
    simpa only [d259486, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259486, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29054 p hg
    simpa only [d259486, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30240 (p : Pattern) (guard : d259487 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259471 p = 1 := by simpa only [d259487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30191 p hg
    simpa only [d259487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259486 p = 1 := by simpa only [d259487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30239 p hg
    simpa only [d259487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30241 (p : Pattern) (guard : d259313 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259301 p = 1 := by simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30208 p hg
    simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29016 p hg
    simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30242 (p : Pattern) (guard : d259488 p = 1) : d47652 p ≤ (-1 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29016 p hg
    simpa only [d259488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259313 p = 1 := by simpa only [d259488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30241 p hg
    simpa only [d259488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30243 (p : Pattern) (guard : d259314 p = 1) : d47797 p ≤ (-1 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259313 p = 1 := by simpa only [d259314, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29897 p hg
    simpa only [d259314, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259314, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d259314, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30244 (p : Pattern) (guard : d259489 p = 1) : d47798 p ≤ (-1 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259488 p = 1 := by simpa only [d259489, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30242 p hg
    simpa only [d259489, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259314 p = 1 := by simpa only [d259489, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30243 p hg
    simpa only [d259489, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30245 (p : Pattern) (guard : d259313 p = 1) : d47677 p ≤ (-1 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259301 p = 1 := by simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30219 p hg
    simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29049 p hg
    simpa only [d259313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30246 (p : Pattern) (guard : d259314 p = 1) : d47682 p ≤ (-1 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259313 p = 1 := by simpa only [d259314, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30245 p hg
    simpa only [d259314, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259314, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259314, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30247 (p : Pattern) (guard : d259315 p = 1) : d47683 p ≤ (-1 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259314 p = 1 := by simpa only [d259315, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30246 p hg
    simpa only [d259315, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259315, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d259315, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30248 (p : Pattern) (guard : d259490 p = 1) : d47799 p ≤ (-1 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d259489 p = 1 := by simpa only [d259490, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30244 p hg
    simpa only [d259490, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259315 p = 1 := by simpa only [d259490, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30247 p hg
    simpa only [d259490, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30249 (p : Pattern) (guard : d259491 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259490 p = 1 := by simpa only [d259491, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30248 p hg
    simpa only [d259491, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259491, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29054 p hg
    simpa only [d259491, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
