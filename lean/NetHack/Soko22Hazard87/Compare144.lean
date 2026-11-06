import NetHack.Soko22Hazard87.Compare143
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare36000 (p : Pattern) (guard : d316479 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d316478 p = 1 := by simpa only [d316479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35999 p hg
    simpa only [d316479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d316479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36001 (p : Pattern) (guard : d316480 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d316479 p = 1 := by simpa only [d316480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36000 p hg
    simpa only [d316480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d316480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36002 (p : Pattern) (guard : d316481 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316476 p = 1 := by simpa only [d316481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35993 p hg
    simpa only [d316481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316480 p = 1 := by simpa only [d316481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36001 p hg
    simpa only [d316481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36003 (p : Pattern) (guard : d316482 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d316481 p = 1 := by simpa only [d316482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36002 p hg
    simpa only [d316482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d316482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36004 (p : Pattern) (guard : d316483 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d316472 p = 1 := by simpa only [d316483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35989 p hg
    simpa only [d316483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d316483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36005 (p : Pattern) (guard : d316484 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d316483 p = 1 := by simpa only [d316484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36004 p hg
    simpa only [d316484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d316484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36006 (p : Pattern) (guard : d316485 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d316484 p = 1 := by simpa only [d316485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36005 p hg
    simpa only [d316485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d316485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36007 (p : Pattern) (guard : d316486 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d316485 p = 1 := by simpa only [d316486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36006 p hg
    simpa only [d316486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d316486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36008 (p : Pattern) (guard : d316487 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316486 p = 1 := by simpa only [d316487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36007 p hg
    simpa only [d316487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d316487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36009 (p : Pattern) (guard : d316488 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d316487 p = 1 := by simpa only [d316488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36008 p hg
    simpa only [d316488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d316488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36010 (p : Pattern) (guard : d316489 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d316482 p = 1 := by simpa only [d316489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36003 p hg
    simpa only [d316489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316488 p = 1 := by simpa only [d316489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36009 p hg
    simpa only [d316489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36011 (p : Pattern) (guard : d316490 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d316490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316489 p = 1 := by simpa only [d316490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36010 p hg
    simpa only [d316490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36012 (p : Pattern) (guard : d316491 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d316491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316490 p = 1 := by simpa only [d316491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36011 p hg
    simpa only [d316491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36013 (p : Pattern) (guard : d316492 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316492, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d316492, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316491 p = 1 := by simpa only [d316492, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36012 p hg
    simpa only [d316492, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36014 (p : Pattern) (guard : d316493 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d316493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316492 p = 1 := by simpa only [d316493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36013 p hg
    simpa only [d316493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36015 (p : Pattern) (guard : d286318 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d286300 p = 1 := by simpa only [d286318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35997 p hg
    simpa only [d286318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d286318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36016 (p : Pattern) (guard : d286319 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d286318 p = 1 := by simpa only [d286319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36015 p hg
    simpa only [d286319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d286319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36017 (p : Pattern) (guard : d286320 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d286319 p = 1 := by simpa only [d286320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36016 p hg
    simpa only [d286320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d286320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36018 (p : Pattern) (guard : d286321 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d286320 p = 1 := by simpa only [d286321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36017 p hg
    simpa only [d286321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d286321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36019 (p : Pattern) (guard : d286322 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d286321 p = 1 := by simpa only [d286322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36018 p hg
    simpa only [d286322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d286322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36020 (p : Pattern) (guard : d286323 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d286323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286322 p = 1 := by simpa only [d286323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36019 p hg
    simpa only [d286323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36021 (p : Pattern) (guard : d286324 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d286323 p = 1 := by simpa only [d286324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36020 p hg
    simpa only [d286324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d286324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36022 (p : Pattern) (guard : d286325 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d286325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286324 p = 1 := by simpa only [d286325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36021 p hg
    simpa only [d286325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36023 (p : Pattern) (guard : d286326 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d286326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286325 p = 1 := by simpa only [d286326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36022 p hg
    simpa only [d286326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36024 (p : Pattern) (guard : d286327 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286327, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d286327, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286326 p = 1 := by simpa only [d286327, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36023 p hg
    simpa only [d286327, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36025 (p : Pattern) (guard : d286328 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d286328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286327 p = 1 := by simpa only [d286328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36024 p hg
    simpa only [d286328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36026 (p : Pattern) (guard : d316494 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d316493 p = 1 := by simpa only [d316494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36014 p hg
    simpa only [d316494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286328 p = 1 := by simpa only [d316494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36025 p hg
    simpa only [d316494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36027 (p : Pattern) (guard : d316495 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d316494 p = 1 := by simpa only [d316495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36026 p hg
    simpa only [d316495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d316495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36028 (p : Pattern) (guard : d316496 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d316495 p = 1 := by simpa only [d316496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36027 p hg
    simpa only [d316496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d316496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36029 (p : Pattern) (guard : d316497 p = 1) : d50492 p ≤ (3 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d316496 p = 1 := by simpa only [d316497, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36028 p hg
    simpa only [d316497, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316497, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35067 p hg
    simpa only [d316497, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36030 (p : Pattern) (guard : d316498 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d316442 p = 1 := by simpa only [d316498, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35902 p hg
    simpa only [d316498, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316497 p = 1 := by simpa only [d316498, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36029 p hg
    simpa only [d316498, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36031 (p : Pattern) (guard : d316499 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d316499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316498 p = 1 := by simpa only [d316499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36030 p hg
    simpa only [d316499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36032 (p : Pattern) (guard : d316500 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d316500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316499 p = 1 := by simpa only [d316500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36031 p hg
    simpa only [d316500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36033 (p : Pattern) (guard : d316501 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d316501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316500 p = 1 := by simpa only [d316501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36032 p hg
    simpa only [d316501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36034 (p : Pattern) (guard : d316502 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d316502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316501 p = 1 := by simpa only [d316502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36033 p hg
    simpa only [d316502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36035 (p : Pattern) (guard : d316503 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d316503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316502 p = 1 := by simpa only [d316503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36034 p hg
    simpa only [d316503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36036 (p : Pattern) (guard : d316504 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d316504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316503 p = 1 := by simpa only [d316504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36035 p hg
    simpa only [d316504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36037 (p : Pattern) (guard : d316505 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d316505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316504 p = 1 := by simpa only [d316505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36036 p hg
    simpa only [d316505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36038 (p : Pattern) (guard : d316506 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d316314 p = 1 := by simpa only [d316506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35584 p hg
    simpa only [d316506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316505 p = 1 := by simpa only [d316506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36037 p hg
    simpa only [d316506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36039 (p : Pattern) (guard : d40149 p = 1) : d47617 p ≤ (3 : Int) + d47617 p := by
  omega
theorem compare36040 (p : Pattern) (guard : d317407 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d40149 p = 1 := by simpa only [d317407, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36039 p hg
    simpa only [d317407, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317407, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34870 p hg
    simpa only [d317407, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36041 (p : Pattern) (guard : d317408 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34868 p hg
    simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317407 p = 1 := by simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36040 p hg
    simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36042 (p : Pattern) (guard : d317409 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d317408 p = 1 := by simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36041 p hg
    simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34868 p hg
    simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36043 (p : Pattern) (guard : d317410 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d317409 p = 1 := by simpa only [d317410, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36042 p hg
    simpa only [d317410, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317410, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34874 p hg
    simpa only [d317410, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36044 (p : Pattern) (guard : d317411 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d286613 p = 1 := by simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35318 p hg
    simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317410 p = 1 := by simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36043 p hg
    simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36045 (p : Pattern) (guard : d317412 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317411 p = 1 := by simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36044 p hg
    simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316231 p = 1 := by simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35325 p hg
    simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36046 (p : Pattern) (guard : d317413 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317412 p = 1 := by simpa only [d317413, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36045 p hg
    simpa only [d317413, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317413, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34879 p hg
    simpa only [d317413, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36047 (p : Pattern) (guard : d317414 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316356 p = 1 := by simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35668 p hg
    simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317413 p = 1 := by simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36046 p hg
    simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36048 (p : Pattern) (guard : d317415 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317414 p = 1 := by simpa only [d317415, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36047 p hg
    simpa only [d317415, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317415, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d317415, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36049 (p : Pattern) (guard : d317416 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317415 p = 1 := by simpa only [d317416, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36048 p hg
    simpa only [d317416, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317416, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d317416, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36050 (p : Pattern) (guard : d317417 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317417, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d317417, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317416 p = 1 := by simpa only [d317417, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36049 p hg
    simpa only [d317417, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36051 (p : Pattern) (guard : d317418 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317417 p = 1 := by simpa only [d317418, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36050 p hg
    simpa only [d317418, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317418, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d317418, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36052 (p : Pattern) (guard : d317419 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317413 p = 1 := by simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36046 p hg
    simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316366 p = 1 := by simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35681 p hg
    simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36053 (p : Pattern) (guard : d317420 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317419 p = 1 := by simpa only [d317420, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36052 p hg
    simpa only [d317420, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317420, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d317420, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36054 (p : Pattern) (guard : d317421 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317420 p = 1 := by simpa only [d317421, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36053 p hg
    simpa only [d317421, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317421, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d317421, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36055 (p : Pattern) (guard : d317422 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317422, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d317422, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317421 p = 1 := by simpa only [d317422, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36054 p hg
    simpa only [d317422, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36056 (p : Pattern) (guard : d317423 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317422 p = 1 := by simpa only [d317423, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36055 p hg
    simpa only [d317423, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317423, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d317423, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36057 (p : Pattern) (guard : d317424 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317418 p = 1 := by simpa only [d317424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36051 p hg
    simpa only [d317424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317423 p = 1 := by simpa only [d317424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36056 p hg
    simpa only [d317424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36058 (p : Pattern) (guard : d317425 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317410 p = 1 := by simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36043 p hg
    simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34875 p hg
    simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36059 (p : Pattern) (guard : d317426 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317425 p = 1 := by simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36058 p hg
    simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34877 p hg
    simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36060 (p : Pattern) (guard : d317427 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317426 p = 1 := by simpa only [d317427, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36059 p hg
    simpa only [d317427, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317427, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34879 p hg
    simpa only [d317427, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36061 (p : Pattern) (guard : d317428 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317427 p = 1 := by simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36060 p hg
    simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34881 p hg
    simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36062 (p : Pattern) (guard : d317429 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317428 p = 1 := by simpa only [d317429, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36061 p hg
    simpa only [d317429, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317429, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d317429, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36063 (p : Pattern) (guard : d317430 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317429 p = 1 := by simpa only [d317430, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36062 p hg
    simpa only [d317430, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317430, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d317430, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36064 (p : Pattern) (guard : d317431 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317431, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d317431, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317430 p = 1 := by simpa only [d317431, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36063 p hg
    simpa only [d317431, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36065 (p : Pattern) (guard : d317432 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317431 p = 1 := by simpa only [d317432, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36064 p hg
    simpa only [d317432, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317432, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d317432, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36066 (p : Pattern) (guard : d317433 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316380 p = 1 := by simpa only [d317433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35695 p hg
    simpa only [d317433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317432 p = 1 := by simpa only [d317433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36065 p hg
    simpa only [d317433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36067 (p : Pattern) (guard : d317434 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317424 p = 1 := by simpa only [d317434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36057 p hg
    simpa only [d317434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317433 p = 1 := by simpa only [d317434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36066 p hg
    simpa only [d317434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36068 (p : Pattern) (guard : d317435 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317410 p = 1 := by simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36043 p hg
    simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36069 (p : Pattern) (guard : d317436 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317435 p = 1 := by simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36068 p hg
    simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34877 p hg
    simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36070 (p : Pattern) (guard : d317437 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317436 p = 1 := by simpa only [d317437, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36069 p hg
    simpa only [d317437, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317437, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34879 p hg
    simpa only [d317437, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36071 (p : Pattern) (guard : d317438 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317413 p = 1 := by simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36046 p hg
    simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317437 p = 1 := by simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36070 p hg
    simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36072 (p : Pattern) (guard : d317439 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317438 p = 1 := by simpa only [d317439, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36071 p hg
    simpa only [d317439, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317439, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d317439, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36073 (p : Pattern) (guard : d317440 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317439 p = 1 := by simpa only [d317440, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36072 p hg
    simpa only [d317440, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317440, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d317440, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36074 (p : Pattern) (guard : d317441 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317441, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d317441, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317440 p = 1 := by simpa only [d317441, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36073 p hg
    simpa only [d317441, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36075 (p : Pattern) (guard : d317442 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317441 p = 1 := by simpa only [d317442, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36074 p hg
    simpa only [d317442, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317442, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d317442, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36076 (p : Pattern) (guard : d317443 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317437 p = 1 := by simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36070 p hg
    simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34881 p hg
    simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36077 (p : Pattern) (guard : d317444 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317443 p = 1 := by simpa only [d317444, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36076 p hg
    simpa only [d317444, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317444, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d317444, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36078 (p : Pattern) (guard : d317445 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317444 p = 1 := by simpa only [d317445, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36077 p hg
    simpa only [d317445, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317445, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d317445, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36079 (p : Pattern) (guard : d317446 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317446, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d317446, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317445 p = 1 := by simpa only [d317446, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36078 p hg
    simpa only [d317446, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36080 (p : Pattern) (guard : d317447 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317446 p = 1 := by simpa only [d317447, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36079 p hg
    simpa only [d317447, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317447, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d317447, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36081 (p : Pattern) (guard : d317448 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317442 p = 1 := by simpa only [d317448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36075 p hg
    simpa only [d317448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317447 p = 1 := by simpa only [d317448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36080 p hg
    simpa only [d317448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36082 (p : Pattern) (guard : d317449 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317432 p = 1 := by simpa only [d317449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36065 p hg
    simpa only [d317449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34890 p hg
    simpa only [d317449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36083 (p : Pattern) (guard : d317450 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317448 p = 1 := by simpa only [d317450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36081 p hg
    simpa only [d317450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317449 p = 1 := by simpa only [d317450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36082 p hg
    simpa only [d317450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36084 (p : Pattern) (guard : d317451 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317434 p = 1 := by simpa only [d317451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36067 p hg
    simpa only [d317451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317450 p = 1 := by simpa only [d317451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36083 p hg
    simpa only [d317451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36085 (p : Pattern) (guard : d317452 p = 1) : d50227 p ≤ (3 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317452, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d317452, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317451 p = 1 := by simpa only [d317452, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36084 p hg
    simpa only [d317452, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36086 (p : Pattern) (guard : d317453 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317453, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34865 p hg
    simpa only [d317453, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317452 p = 1 := by simpa only [d317453, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36085 p hg
    simpa only [d317453, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36087 (p : Pattern) (guard : d317454 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317447 p = 1 := by simpa only [d317454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36080 p hg
    simpa only [d317454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34890 p hg
    simpa only [d317454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36088 (p : Pattern) (guard : d317455 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317454 p = 1 := by simpa only [d317455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36087 p hg
    simpa only [d317455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34890 p hg
    simpa only [d317455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36089 (p : Pattern) (guard : d317456 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317450 p = 1 := by simpa only [d317456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36083 p hg
    simpa only [d317456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317455 p = 1 := by simpa only [d317456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36088 p hg
    simpa only [d317456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36090 (p : Pattern) (guard : d317457 p = 1) : d50227 p ≤ (3 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317457, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d317457, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317456 p = 1 := by simpa only [d317457, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36089 p hg
    simpa only [d317457, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36091 (p : Pattern) (guard : d317458 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317458, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34865 p hg
    simpa only [d317458, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317457 p = 1 := by simpa only [d317458, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36090 p hg
    simpa only [d317458, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36092 (p : Pattern) (guard : d317459 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317453 p = 1 := by simpa only [d317459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36086 p hg
    simpa only [d317459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317458 p = 1 := by simpa only [d317459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36091 p hg
    simpa only [d317459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36093 (p : Pattern) (guard : d317460 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317458 p = 1 := by simpa only [d317460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36091 p hg
    simpa only [d317460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d317460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36094 (p : Pattern) (guard : d317461 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317459 p = 1 := by simpa only [d317461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36092 p hg
    simpa only [d317461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317460 p = 1 := by simpa only [d317461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36093 p hg
    simpa only [d317461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36095 (p : Pattern) (guard : d317462 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317461 p = 1 := by simpa only [d317462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36094 p hg
    simpa only [d317462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d317462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36096 (p : Pattern) (guard : d317463 p = 1) : d50272 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317462 p = 1 := by simpa only [d317463, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36095 p hg
    simpa only [d317463, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317463, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d317463, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36097 (p : Pattern) (guard : d317464 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317464, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d317464, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317463 p = 1 := by simpa only [d317464, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36096 p hg
    simpa only [d317464, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36098 (p : Pattern) (guard : d317465 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317460 p = 1 := by simpa only [d317465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36093 p hg
    simpa only [d317465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d317465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36099 (p : Pattern) (guard : d317466 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317465 p = 1 := by simpa only [d317466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36098 p hg
    simpa only [d317466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d317466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36100 (p : Pattern) (guard : d317467 p = 1) : d50272 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317466 p = 1 := by simpa only [d317467, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36099 p hg
    simpa only [d317467, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317467, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d317467, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36101 (p : Pattern) (guard : d317468 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317468, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d317468, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317467 p = 1 := by simpa only [d317468, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36100 p hg
    simpa only [d317468, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36102 (p : Pattern) (guard : d317469 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317464 p = 1 := by simpa only [d317469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36097 p hg
    simpa only [d317469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317468 p = 1 := by simpa only [d317469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36101 p hg
    simpa only [d317469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36103 (p : Pattern) (guard : d317470 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317469 p = 1 := by simpa only [d317470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36102 p hg
    simpa only [d317470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36104 (p : Pattern) (guard : d317471 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317470 p = 1 := by simpa only [d317471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36103 p hg
    simpa only [d317471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36105 (p : Pattern) (guard : d317472 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317471 p = 1 := by simpa only [d317472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36104 p hg
    simpa only [d317472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36106 (p : Pattern) (guard : d317473 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317468 p = 1 := by simpa only [d317473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36101 p hg
    simpa only [d317473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36107 (p : Pattern) (guard : d317474 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317473 p = 1 := by simpa only [d317474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36106 p hg
    simpa only [d317474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36108 (p : Pattern) (guard : d317475 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317474 p = 1 := by simpa only [d317475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36107 p hg
    simpa only [d317475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36109 (p : Pattern) (guard : d317476 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317475 p = 1 := by simpa only [d317476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36108 p hg
    simpa only [d317476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36110 (p : Pattern) (guard : d317477 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317472 p = 1 := by simpa only [d317477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36105 p hg
    simpa only [d317477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317476 p = 1 := by simpa only [d317477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36109 p hg
    simpa only [d317477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36111 (p : Pattern) (guard : d317478 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317477 p = 1 := by simpa only [d317478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36110 p hg
    simpa only [d317478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36112 (p : Pattern) (guard : d317479 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317478 p = 1 := by simpa only [d317479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36111 p hg
    simpa only [d317479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36113 (p : Pattern) (guard : d317480 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317479 p = 1 := by simpa only [d317480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36112 p hg
    simpa only [d317480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36114 (p : Pattern) (guard : d317481 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317480 p = 1 := by simpa only [d317481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36113 p hg
    simpa only [d317481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36115 (p : Pattern) (guard : d317482 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317482, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317482, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317481 p = 1 := by simpa only [d317482, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36114 p hg
    simpa only [d317482, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36116 (p : Pattern) (guard : d317483 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d317483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317482 p = 1 := by simpa only [d317483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36115 p hg
    simpa only [d317483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36117 (p : Pattern) (guard : d317484 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d317483 p = 1 := by simpa only [d317484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36116 p hg
    simpa only [d317484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d317484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36118 (p : Pattern) (guard : d317453 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317453, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d317453, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317452 p = 1 := by simpa only [d317453, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36085 p hg
    simpa only [d317453, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36119 (p : Pattern) (guard : d317458 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317458, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d317458, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317457 p = 1 := by simpa only [d317458, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36090 p hg
    simpa only [d317458, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36120 (p : Pattern) (guard : d317459 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317453 p = 1 := by simpa only [d317459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36118 p hg
    simpa only [d317459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317458 p = 1 := by simpa only [d317459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36119 p hg
    simpa only [d317459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36121 (p : Pattern) (guard : d317460 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317458 p = 1 := by simpa only [d317460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36119 p hg
    simpa only [d317460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d317460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36122 (p : Pattern) (guard : d317461 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317459 p = 1 := by simpa only [d317461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36120 p hg
    simpa only [d317461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317460 p = 1 := by simpa only [d317461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36121 p hg
    simpa only [d317461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36123 (p : Pattern) (guard : d317462 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317461 p = 1 := by simpa only [d317462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36122 p hg
    simpa only [d317462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d317462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36124 (p : Pattern) (guard : d317463 p = 1) : d50250 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317462 p = 1 := by simpa only [d317463, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36123 p hg
    simpa only [d317463, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317463, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d317463, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36125 (p : Pattern) (guard : d317464 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317464, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34913 p hg
    simpa only [d317464, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317463 p = 1 := by simpa only [d317464, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36124 p hg
    simpa only [d317464, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36126 (p : Pattern) (guard : d317465 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317460 p = 1 := by simpa only [d317465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36121 p hg
    simpa only [d317465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d317465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36127 (p : Pattern) (guard : d317466 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317465 p = 1 := by simpa only [d317466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36126 p hg
    simpa only [d317466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d317466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36128 (p : Pattern) (guard : d317467 p = 1) : d50250 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317466 p = 1 := by simpa only [d317467, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36127 p hg
    simpa only [d317467, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317467, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d317467, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36129 (p : Pattern) (guard : d317468 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317468, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34913 p hg
    simpa only [d317468, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317467 p = 1 := by simpa only [d317468, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36128 p hg
    simpa only [d317468, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36130 (p : Pattern) (guard : d317469 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317464 p = 1 := by simpa only [d317469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36125 p hg
    simpa only [d317469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317468 p = 1 := by simpa only [d317469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36129 p hg
    simpa only [d317469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36131 (p : Pattern) (guard : d317470 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317469 p = 1 := by simpa only [d317470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36130 p hg
    simpa only [d317470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36132 (p : Pattern) (guard : d317471 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317470 p = 1 := by simpa only [d317471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36131 p hg
    simpa only [d317471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36133 (p : Pattern) (guard : d317472 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317471 p = 1 := by simpa only [d317472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36132 p hg
    simpa only [d317472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36134 (p : Pattern) (guard : d317473 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317468 p = 1 := by simpa only [d317473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36129 p hg
    simpa only [d317473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36135 (p : Pattern) (guard : d317474 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317473 p = 1 := by simpa only [d317474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36134 p hg
    simpa only [d317474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36136 (p : Pattern) (guard : d317475 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317474 p = 1 := by simpa only [d317475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36135 p hg
    simpa only [d317475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36137 (p : Pattern) (guard : d317476 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317475 p = 1 := by simpa only [d317476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36136 p hg
    simpa only [d317476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36138 (p : Pattern) (guard : d317477 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317472 p = 1 := by simpa only [d317477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36133 p hg
    simpa only [d317477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317476 p = 1 := by simpa only [d317477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36137 p hg
    simpa only [d317477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36139 (p : Pattern) (guard : d317478 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317477 p = 1 := by simpa only [d317478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36138 p hg
    simpa only [d317478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36140 (p : Pattern) (guard : d317479 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317478 p = 1 := by simpa only [d317479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36139 p hg
    simpa only [d317479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36141 (p : Pattern) (guard : d317480 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317479 p = 1 := by simpa only [d317480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36140 p hg
    simpa only [d317480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36142 (p : Pattern) (guard : d317481 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317480 p = 1 := by simpa only [d317481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36141 p hg
    simpa only [d317481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36143 (p : Pattern) (guard : d317485 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317471 p = 1 := by simpa only [d317485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36104 p hg
    simpa only [d317485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36144 (p : Pattern) (guard : d317486 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317475 p = 1 := by simpa only [d317486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36108 p hg
    simpa only [d317486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36145 (p : Pattern) (guard : d317487 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317485 p = 1 := by simpa only [d317487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36143 p hg
    simpa only [d317487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317486 p = 1 := by simpa only [d317487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36144 p hg
    simpa only [d317487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36146 (p : Pattern) (guard : d317488 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317487 p = 1 := by simpa only [d317488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36145 p hg
    simpa only [d317488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36147 (p : Pattern) (guard : d317489 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317488 p = 1 := by simpa only [d317489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36146 p hg
    simpa only [d317489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36148 (p : Pattern) (guard : d317490 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317489 p = 1 := by simpa only [d317490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36147 p hg
    simpa only [d317490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36149 (p : Pattern) (guard : d317491 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317490 p = 1 := by simpa only [d317491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36148 p hg
    simpa only [d317491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36150 (p : Pattern) (guard : d317492 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d317481 p = 1 := by simpa only [d317492, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36142 p hg
    simpa only [d317492, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317491 p = 1 := by simpa only [d317492, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36149 p hg
    simpa only [d317492, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36151 (p : Pattern) (guard : d317493 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d317482 p = 1 := by simpa only [d317493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36115 p hg
    simpa only [d317493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317492 p = 1 := by simpa only [d317493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36150 p hg
    simpa only [d317493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36152 (p : Pattern) (guard : d317494 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d317493 p = 1 := by simpa only [d317494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36151 p hg
    simpa only [d317494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d317494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36153 (p : Pattern) (guard : d317495 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d317484 p = 1 := by simpa only [d317495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36117 p hg
    simpa only [d317495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317494 p = 1 := by simpa only [d317495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36152 p hg
    simpa only [d317495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36154 (p : Pattern) (guard : d317496 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317470 p = 1 := by simpa only [d317496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36103 p hg
    simpa only [d317496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36155 (p : Pattern) (guard : d317497 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317496 p = 1 := by simpa only [d317497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36154 p hg
    simpa only [d317497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36156 (p : Pattern) (guard : d317498 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317474 p = 1 := by simpa only [d317498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36107 p hg
    simpa only [d317498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36157 (p : Pattern) (guard : d317499 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317498 p = 1 := by simpa only [d317499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36156 p hg
    simpa only [d317499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36158 (p : Pattern) (guard : d317500 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317497 p = 1 := by simpa only [d317500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36155 p hg
    simpa only [d317500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317499 p = 1 := by simpa only [d317500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36157 p hg
    simpa only [d317500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36159 (p : Pattern) (guard : d317501 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317500 p = 1 := by simpa only [d317501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36158 p hg
    simpa only [d317501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36160 (p : Pattern) (guard : d317502 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317501 p = 1 := by simpa only [d317502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36159 p hg
    simpa only [d317502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36161 (p : Pattern) (guard : d317503 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317502 p = 1 := by simpa only [d317503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36160 p hg
    simpa only [d317503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36162 (p : Pattern) (guard : d317504 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317469 p = 1 := by simpa only [d317504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36102 p hg
    simpa only [d317504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36163 (p : Pattern) (guard : d317505 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317504 p = 1 := by simpa only [d317505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36162 p hg
    simpa only [d317505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36164 (p : Pattern) (guard : d317506 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317505 p = 1 := by simpa only [d317506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36163 p hg
    simpa only [d317506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36165 (p : Pattern) (guard : d317507 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317473 p = 1 := by simpa only [d317507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36106 p hg
    simpa only [d317507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36166 (p : Pattern) (guard : d317508 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317507 p = 1 := by simpa only [d317508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36165 p hg
    simpa only [d317508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36167 (p : Pattern) (guard : d317509 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317508 p = 1 := by simpa only [d317509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36166 p hg
    simpa only [d317509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36168 (p : Pattern) (guard : d317510 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317506 p = 1 := by simpa only [d317510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36164 p hg
    simpa only [d317510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317509 p = 1 := by simpa only [d317510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36167 p hg
    simpa only [d317510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36169 (p : Pattern) (guard : d317511 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317510 p = 1 := by simpa only [d317511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36168 p hg
    simpa only [d317511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36170 (p : Pattern) (guard : d317512 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317511 p = 1 := by simpa only [d317512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36169 p hg
    simpa only [d317512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36171 (p : Pattern) (guard : d34355 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34354 p = 1 := by simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35665 p hg
    simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36172 (p : Pattern) (guard : d34356 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34355 p = 1 := by simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36171 p hg
    simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36173 (p : Pattern) (guard : d34357 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d34356 p = 1 := by simpa only [d34357, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36172 p hg
    simpa only [d34357, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34357, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34879 p hg
    simpa only [d34357, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36174 (p : Pattern) (guard : d316571 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d34357 p = 1 := by simpa only [d316571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36173 p hg
    simpa only [d316571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316356 p = 1 := by simpa only [d316571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35668 p hg
    simpa only [d316571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36175 (p : Pattern) (guard : d316572 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316571 p = 1 := by simpa only [d316572, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36174 p hg
    simpa only [d316572, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316572, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d316572, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36176 (p : Pattern) (guard : d316573 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316572 p = 1 := by simpa only [d316573, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36175 p hg
    simpa only [d316573, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316573, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d316573, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36177 (p : Pattern) (guard : d316574 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316574, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d316574, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316573 p = 1 := by simpa only [d316574, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36176 p hg
    simpa only [d316574, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36178 (p : Pattern) (guard : d316575 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316574 p = 1 := by simpa only [d316575, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36177 p hg
    simpa only [d316575, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316575, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d316575, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36179 (p : Pattern) (guard : d34366 p = 1) : d47617 p ≤ (3 : Int) + d47617 p := by
  omega
theorem compare36180 (p : Pattern) (guard : d34367 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d34366 p = 1 := by simpa only [d34367, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36179 p hg
    simpa only [d34367, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34367, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34870 p hg
    simpa only [d34367, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36181 (p : Pattern) (guard : d316576 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34868 p hg
    simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34367 p = 1 := by simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36180 p hg
    simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36182 (p : Pattern) (guard : d316577 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d316576 p = 1 := by simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36181 p hg
    simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34868 p hg
    simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36183 (p : Pattern) (guard : d316578 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d316577 p = 1 := by simpa only [d316578, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36182 p hg
    simpa only [d316578, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316578, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34874 p hg
    simpa only [d316578, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36184 (p : Pattern) (guard : d316579 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316578 p = 1 := by simpa only [d316579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36183 p hg
    simpa only [d316579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316363 p = 1 := by simpa only [d316579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35678 p hg
    simpa only [d316579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36185 (p : Pattern) (guard : d316580 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316579 p = 1 := by simpa only [d316580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36184 p hg
    simpa only [d316580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d316580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36186 (p : Pattern) (guard : d316581 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316580 p = 1 := by simpa only [d316581, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36185 p hg
    simpa only [d316581, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316581, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34879 p hg
    simpa only [d316581, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36187 (p : Pattern) (guard : d316582 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316356 p = 1 := by simpa only [d316582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35668 p hg
    simpa only [d316582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316581 p = 1 := by simpa only [d316582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36186 p hg
    simpa only [d316582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36188 (p : Pattern) (guard : d316583 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316582 p = 1 := by simpa only [d316583, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36187 p hg
    simpa only [d316583, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316583, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d316583, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36189 (p : Pattern) (guard : d316584 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316583 p = 1 := by simpa only [d316584, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36188 p hg
    simpa only [d316584, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316584, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d316584, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36190 (p : Pattern) (guard : d316585 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316585, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d316585, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316584 p = 1 := by simpa only [d316585, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36189 p hg
    simpa only [d316585, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36191 (p : Pattern) (guard : d316586 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316585 p = 1 := by simpa only [d316586, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36190 p hg
    simpa only [d316586, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316586, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d316586, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36192 (p : Pattern) (guard : d316587 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316575 p = 1 := by simpa only [d316587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36178 p hg
    simpa only [d316587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316586 p = 1 := by simpa only [d316587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36191 p hg
    simpa only [d316587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36193 (p : Pattern) (guard : d316588 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316578 p = 1 := by simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36183 p hg
    simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36194 (p : Pattern) (guard : d316589 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316588 p = 1 := by simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36193 p hg
    simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36195 (p : Pattern) (guard : d316590 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316589 p = 1 := by simpa only [d316590, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36194 p hg
    simpa only [d316590, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316590, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34879 p hg
    simpa only [d316590, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36196 (p : Pattern) (guard : d316591 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316590 p = 1 := by simpa only [d316591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36195 p hg
    simpa only [d316591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316581 p = 1 := by simpa only [d316591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36186 p hg
    simpa only [d316591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36197 (p : Pattern) (guard : d316592 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316591 p = 1 := by simpa only [d316592, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36196 p hg
    simpa only [d316592, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316592, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d316592, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36198 (p : Pattern) (guard : d316593 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316592 p = 1 := by simpa only [d316593, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36197 p hg
    simpa only [d316593, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316593, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d316593, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36199 (p : Pattern) (guard : d316594 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316594, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d316594, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316593 p = 1 := by simpa only [d316594, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36198 p hg
    simpa only [d316594, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36200 (p : Pattern) (guard : d316595 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316594 p = 1 := by simpa only [d316595, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36199 p hg
    simpa only [d316595, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316595, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d316595, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36201 (p : Pattern) (guard : d316596 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316595 p = 1 := by simpa only [d316596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36200 p hg
    simpa only [d316596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316380 p = 1 := by simpa only [d316596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35695 p hg
    simpa only [d316596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36202 (p : Pattern) (guard : d316597 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d316587 p = 1 := by simpa only [d316597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36192 p hg
    simpa only [d316597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316596 p = 1 := by simpa only [d316597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36201 p hg
    simpa only [d316597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36203 (p : Pattern) (guard : d317513 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d316597 p = 1 := by simpa only [d317513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36202 p hg
    simpa only [d317513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317434 p = 1 := by simpa only [d317513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36067 p hg
    simpa only [d317513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36204 (p : Pattern) (guard : d317514 p = 1) : d50227 p ≤ (3 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317514, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d317514, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317513 p = 1 := by simpa only [d317514, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36203 p hg
    simpa only [d317514, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36205 (p : Pattern) (guard : d317515 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317515, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34865 p hg
    simpa only [d317515, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317514 p = 1 := by simpa only [d317515, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36204 p hg
    simpa only [d317515, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36206 (p : Pattern) (guard : d317516 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317433 p = 1 := by simpa only [d317516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36066 p hg
    simpa only [d317516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317449 p = 1 := by simpa only [d317516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36082 p hg
    simpa only [d317516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36207 (p : Pattern) (guard : d317517 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317434 p = 1 := by simpa only [d317517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36067 p hg
    simpa only [d317517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317516 p = 1 := by simpa only [d317517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36206 p hg
    simpa only [d317517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36208 (p : Pattern) (guard : d317518 p = 1) : d50227 p ≤ (3 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317518, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d317518, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317517 p = 1 := by simpa only [d317518, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36207 p hg
    simpa only [d317518, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36209 (p : Pattern) (guard : d317519 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317519, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34865 p hg
    simpa only [d317519, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317518 p = 1 := by simpa only [d317519, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36208 p hg
    simpa only [d317519, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36210 (p : Pattern) (guard : d317520 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317515 p = 1 := by simpa only [d317520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36205 p hg
    simpa only [d317520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317519 p = 1 := by simpa only [d317520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36209 p hg
    simpa only [d317520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36211 (p : Pattern) (guard : d317521 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317520 p = 1 := by simpa only [d317521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36210 p hg
    simpa only [d317521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317459 p = 1 := by simpa only [d317521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36092 p hg
    simpa only [d317521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36212 (p : Pattern) (guard : d317522 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317521 p = 1 := by simpa only [d317522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36211 p hg
    simpa only [d317522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d317522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36213 (p : Pattern) (guard : d317523 p = 1) : d50272 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317522 p = 1 := by simpa only [d317523, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36212 p hg
    simpa only [d317523, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317523, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d317523, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36214 (p : Pattern) (guard : d317524 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317524, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d317524, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317523 p = 1 := by simpa only [d317524, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36213 p hg
    simpa only [d317524, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36215 (p : Pattern) (guard : d317525 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317524 p = 1 := by simpa only [d317525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36214 p hg
    simpa only [d317525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317464 p = 1 := by simpa only [d317525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36097 p hg
    simpa only [d317525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36216 (p : Pattern) (guard : d317526 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317525 p = 1 := by simpa only [d317526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36215 p hg
    simpa only [d317526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36217 (p : Pattern) (guard : d317527 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317526 p = 1 := by simpa only [d317527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36216 p hg
    simpa only [d317527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36218 (p : Pattern) (guard : d317528 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317527 p = 1 := by simpa only [d317528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36217 p hg
    simpa only [d317528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36219 (p : Pattern) (guard : d317529 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317528 p = 1 := by simpa only [d317529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36218 p hg
    simpa only [d317529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317472 p = 1 := by simpa only [d317529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36105 p hg
    simpa only [d317529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36220 (p : Pattern) (guard : d317530 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d317529 p = 1 := by simpa only [d317530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36219 p hg
    simpa only [d317530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36221 (p : Pattern) (guard : d317531 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317464 p = 1 := by simpa only [d317531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36097 p hg
    simpa only [d317531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36222 (p : Pattern) (guard : d317532 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317531 p = 1 := by simpa only [d317532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36221 p hg
    simpa only [d317532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36223 (p : Pattern) (guard : d317533 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317532 p = 1 := by simpa only [d317533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36222 p hg
    simpa only [d317533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36224 (p : Pattern) (guard : d317534 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317533 p = 1 := by simpa only [d317534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36223 p hg
    simpa only [d317534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36225 (p : Pattern) (guard : d317535 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317534 p = 1 := by simpa only [d317535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36224 p hg
    simpa only [d317535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36226 (p : Pattern) (guard : d317536 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d317535 p = 1 := by simpa only [d317536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36225 p hg
    simpa only [d317536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36227 (p : Pattern) (guard : d317537 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317530 p = 1 := by simpa only [d317537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36220 p hg
    simpa only [d317537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317536 p = 1 := by simpa only [d317537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36226 p hg
    simpa only [d317537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36228 (p : Pattern) (guard : d317538 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d317512 p = 1 := by simpa only [d317538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36170 p hg
    simpa only [d317538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317537 p = 1 := by simpa only [d317538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36227 p hg
    simpa only [d317538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36229 (p : Pattern) (guard : d317539 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d317503 p = 1 := by simpa only [d317539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36161 p hg
    simpa only [d317539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317538 p = 1 := by simpa only [d317539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36228 p hg
    simpa only [d317539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36230 (p : Pattern) (guard : d317540 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317540, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317540, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317539 p = 1 := by simpa only [d317540, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36229 p hg
    simpa only [d317540, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36231 (p : Pattern) (guard : d317496 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317470 p = 1 := by simpa only [d317496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36131 p hg
    simpa only [d317496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36232 (p : Pattern) (guard : d317497 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317496 p = 1 := by simpa only [d317497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36231 p hg
    simpa only [d317497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36233 (p : Pattern) (guard : d317498 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317474 p = 1 := by simpa only [d317498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36135 p hg
    simpa only [d317498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36234 (p : Pattern) (guard : d317499 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317498 p = 1 := by simpa only [d317499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36233 p hg
    simpa only [d317499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36235 (p : Pattern) (guard : d317500 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317497 p = 1 := by simpa only [d317500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36232 p hg
    simpa only [d317500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317499 p = 1 := by simpa only [d317500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36234 p hg
    simpa only [d317500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36236 (p : Pattern) (guard : d317501 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317500 p = 1 := by simpa only [d317501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36235 p hg
    simpa only [d317501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36237 (p : Pattern) (guard : d317502 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317501 p = 1 := by simpa only [d317502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36236 p hg
    simpa only [d317502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36238 (p : Pattern) (guard : d317503 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317502 p = 1 := by simpa only [d317503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36237 p hg
    simpa only [d317503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36239 (p : Pattern) (guard : d317504 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317469 p = 1 := by simpa only [d317504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36130 p hg
    simpa only [d317504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36240 (p : Pattern) (guard : d317505 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317504 p = 1 := by simpa only [d317505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36239 p hg
    simpa only [d317505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36241 (p : Pattern) (guard : d317506 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317505 p = 1 := by simpa only [d317506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36240 p hg
    simpa only [d317506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36242 (p : Pattern) (guard : d317507 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317473 p = 1 := by simpa only [d317507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36134 p hg
    simpa only [d317507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36243 (p : Pattern) (guard : d317508 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317507 p = 1 := by simpa only [d317508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36242 p hg
    simpa only [d317508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36244 (p : Pattern) (guard : d317509 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317508 p = 1 := by simpa only [d317509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36243 p hg
    simpa only [d317509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36245 (p : Pattern) (guard : d317510 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317506 p = 1 := by simpa only [d317510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36241 p hg
    simpa only [d317510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317509 p = 1 := by simpa only [d317510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36244 p hg
    simpa only [d317510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36246 (p : Pattern) (guard : d317511 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317510 p = 1 := by simpa only [d317511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36245 p hg
    simpa only [d317511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36247 (p : Pattern) (guard : d317512 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317511 p = 1 := by simpa only [d317512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36246 p hg
    simpa only [d317512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36248 (p : Pattern) (guard : d317515 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317515, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d317515, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317514 p = 1 := by simpa only [d317515, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36204 p hg
    simpa only [d317515, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36249 (p : Pattern) (guard : d317519 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317519, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d317519, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317518 p = 1 := by simpa only [d317519, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36208 p hg
    simpa only [d317519, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
