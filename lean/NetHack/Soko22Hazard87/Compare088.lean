import NetHack.Soko22Hazard87.Compare087
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare22000 (p : Pattern) (guard : d179330 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179309 p = 1 := by simpa only [d179330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21947 p hg
    simpa only [d179330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22001 (p : Pattern) (guard : d179331 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179330 p = 1 := by simpa only [d179331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22000 p hg
    simpa only [d179331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22002 (p : Pattern) (guard : d179332 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179331 p = 1 := by simpa only [d179332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22001 p hg
    simpa only [d179332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22003 (p : Pattern) (guard : d179333 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179332 p = 1 := by simpa only [d179333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22002 p hg
    simpa only [d179333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22004 (p : Pattern) (guard : d179334 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179333 p = 1 := by simpa only [d179334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22003 p hg
    simpa only [d179334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22005 (p : Pattern) (guard : d179335 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179334 p = 1 := by simpa only [d179335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22004 p hg
    simpa only [d179335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22006 (p : Pattern) (guard : d179336 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179308 p = 1 := by simpa only [d179336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21946 p hg
    simpa only [d179336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22007 (p : Pattern) (guard : d179337 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179336 p = 1 := by simpa only [d179337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22006 p hg
    simpa only [d179337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22008 (p : Pattern) (guard : d179338 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179337 p = 1 := by simpa only [d179338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22007 p hg
    simpa only [d179338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22009 (p : Pattern) (guard : d179339 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179338 p = 1 := by simpa only [d179339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22008 p hg
    simpa only [d179339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22010 (p : Pattern) (guard : d179340 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179339 p = 1 := by simpa only [d179340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22009 p hg
    simpa only [d179340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22011 (p : Pattern) (guard : d179341 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179340 p = 1 := by simpa only [d179341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22010 p hg
    simpa only [d179341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22012 (p : Pattern) (guard : d179360 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179360, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21649 p hg
    simpa only [d179360, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179359 p = 1 := by simpa only [d179360, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21982 p hg
    simpa only [d179360, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22013 (p : Pattern) (guard : d179361 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179360 p = 1 := by simpa only [d179361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22012 p hg
    simpa only [d179361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179302 p = 1 := by simpa only [d179361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21940 p hg
    simpa only [d179361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22014 (p : Pattern) (guard : d179362 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179361 p = 1 := by simpa only [d179362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22013 p hg
    simpa only [d179362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179303 p = 1 := by simpa only [d179362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21941 p hg
    simpa only [d179362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22015 (p : Pattern) (guard : d179363 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179362 p = 1 := by simpa only [d179363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22014 p hg
    simpa only [d179363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21651 p hg
    simpa only [d179363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22016 (p : Pattern) (guard : d179364 p = 1) : d48329 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179363 p = 1 := by simpa only [d179364, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22015 p hg
    simpa only [d179364, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179364, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d179364, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22017 (p : Pattern) (guard : d179365 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179365, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21648 p hg
    simpa only [d179365, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179364 p = 1 := by simpa only [d179365, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22016 p hg
    simpa only [d179365, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22018 (p : Pattern) (guard : d179366 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179365 p = 1 := by simpa only [d179366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22017 p hg
    simpa only [d179366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179307 p = 1 := by simpa only [d179366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21945 p hg
    simpa only [d179366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22019 (p : Pattern) (guard : d179367 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179366 p = 1 := by simpa only [d179367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22018 p hg
    simpa only [d179367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22020 (p : Pattern) (guard : d179368 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179367 p = 1 := by simpa only [d179368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22019 p hg
    simpa only [d179368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22021 (p : Pattern) (guard : d179369 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179368 p = 1 := by simpa only [d179369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22020 p hg
    simpa only [d179369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22022 (p : Pattern) (guard : d179370 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179369 p = 1 := by simpa only [d179370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22021 p hg
    simpa only [d179370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179311 p = 1 := by simpa only [d179370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21949 p hg
    simpa only [d179370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22023 (p : Pattern) (guard : d179371 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179370 p = 1 := by simpa only [d179371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22022 p hg
    simpa only [d179371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22024 (p : Pattern) (guard : d179372 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179312 p = 1 := by simpa only [d179372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21950 p hg
    simpa only [d179372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22025 (p : Pattern) (guard : d179373 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179371 p = 1 := by simpa only [d179373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22023 p hg
    simpa only [d179373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179372 p = 1 := by simpa only [d179373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22024 p hg
    simpa only [d179373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22026 (p : Pattern) (guard : d179374 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d179341 p = 1 := by simpa only [d179374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22011 p hg
    simpa only [d179374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179373 p = 1 := by simpa only [d179374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22025 p hg
    simpa only [d179374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22027 (p : Pattern) (guard : d179375 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d179335 p = 1 := by simpa only [d179375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22005 p hg
    simpa only [d179375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179374 p = 1 := by simpa only [d179375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22026 p hg
    simpa only [d179375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22028 (p : Pattern) (guard : d179377 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179330 p = 1 := by simpa only [d179377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21965 p hg
    simpa only [d179377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22029 (p : Pattern) (guard : d179378 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179377 p = 1 := by simpa only [d179378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22028 p hg
    simpa only [d179378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22030 (p : Pattern) (guard : d179379 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179378 p = 1 := by simpa only [d179379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22029 p hg
    simpa only [d179379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22031 (p : Pattern) (guard : d179380 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179379 p = 1 := by simpa only [d179380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22030 p hg
    simpa only [d179380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22032 (p : Pattern) (guard : d179381 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179380 p = 1 := by simpa only [d179381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22031 p hg
    simpa only [d179381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22033 (p : Pattern) (guard : d179382 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179337 p = 1 := by simpa only [d179382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21972 p hg
    simpa only [d179382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22034 (p : Pattern) (guard : d179383 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179382 p = 1 := by simpa only [d179383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22033 p hg
    simpa only [d179383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22035 (p : Pattern) (guard : d179384 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179383 p = 1 := by simpa only [d179384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22034 p hg
    simpa only [d179384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22036 (p : Pattern) (guard : d179385 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179384 p = 1 := by simpa only [d179385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22035 p hg
    simpa only [d179385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22037 (p : Pattern) (guard : d179386 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179368 p = 1 := by simpa only [d179386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21991 p hg
    simpa only [d179386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22038 (p : Pattern) (guard : d179387 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179386 p = 1 := by simpa only [d179387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22037 p hg
    simpa only [d179387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179320 p = 1 := by simpa only [d179387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21955 p hg
    simpa only [d179387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22039 (p : Pattern) (guard : d179388 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179387 p = 1 := by simpa only [d179388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22038 p hg
    simpa only [d179388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22040 (p : Pattern) (guard : d179389 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179321 p = 1 := by simpa only [d179389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21956 p hg
    simpa only [d179389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22041 (p : Pattern) (guard : d179390 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179388 p = 1 := by simpa only [d179390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22039 p hg
    simpa only [d179390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179389 p = 1 := by simpa only [d179390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22040 p hg
    simpa only [d179390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22042 (p : Pattern) (guard : d179391 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d179385 p = 1 := by simpa only [d179391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22036 p hg
    simpa only [d179391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179390 p = 1 := by simpa only [d179391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22041 p hg
    simpa only [d179391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22043 (p : Pattern) (guard : d179392 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d179381 p = 1 := by simpa only [d179392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22032 p hg
    simpa only [d179392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179391 p = 1 := by simpa only [d179392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22042 p hg
    simpa only [d179392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22044 (p : Pattern) (guard : d179393 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d179375 p = 1 := by simpa only [d179393, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22027 p hg
    simpa only [d179393, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179392 p = 1 := by simpa only [d179393, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22043 p hg
    simpa only [d179393, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22045 (p : Pattern) (guard : d179394 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d179376 p = 1 := by simpa only [d179394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21999 p hg
    simpa only [d179394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179393 p = 1 := by simpa only [d179394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22044 p hg
    simpa only [d179394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22046 (p : Pattern) (guard : d179395 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d179316 p = 1 := by simpa only [d179395, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21954 p hg
    simpa only [d179395, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179395, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179395, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22047 (p : Pattern) (guard : d179396 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d179395 p = 1 := by simpa only [d179396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22046 p hg
    simpa only [d179396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d179396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22048 (p : Pattern) (guard : d179397 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179394 p = 1 := by simpa only [d179397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22045 p hg
    simpa only [d179397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179396 p = 1 := by simpa only [d179397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22047 p hg
    simpa only [d179397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22049 (p : Pattern) (guard : d179398 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d179397 p = 1 := by simpa only [d179398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22048 p hg
    simpa only [d179398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d179398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22050 (p : Pattern) (guard : d179399 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d179329 p = 1 := by simpa only [d179399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21964 p hg
    simpa only [d179399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179398 p = 1 := by simpa only [d179399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22049 p hg
    simpa only [d179399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22051 (p : Pattern) (guard : d179354 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare22052 (p : Pattern) (guard : d179355 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179354 p = 1 := by simpa only [d179355, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22051 p hg
    simpa only [d179355, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179355, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21684 p hg
    simpa only [d179355, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22053 (p : Pattern) (guard : d179356 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179355 p = 1 := by simpa only [d179356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22052 p hg
    simpa only [d179356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22054 (p : Pattern) (guard : d179357 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179356 p = 1 := by simpa only [d179357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22053 p hg
    simpa only [d179357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22055 (p : Pattern) (guard : d179358 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179357 p = 1 := by simpa only [d179358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22054 p hg
    simpa only [d179358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179214 p = 1 := by simpa only [d179358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21861 p hg
    simpa only [d179358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22056 (p : Pattern) (guard : d179359 p = 1) : d48346 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179359, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21681 p hg
    simpa only [d179359, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179358 p = 1 := by simpa only [d179359, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22055 p hg
    simpa only [d179359, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22057 (p : Pattern) (guard : d179360 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179360, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21680 p hg
    simpa only [d179360, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179359 p = 1 := by simpa only [d179360, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22056 p hg
    simpa only [d179360, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22058 (p : Pattern) (guard : d179300 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179214 p = 1 := by simpa only [d179300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21861 p hg
    simpa only [d179300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22059 (p : Pattern) (guard : d179301 p = 1) : d48346 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179301, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21681 p hg
    simpa only [d179301, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179300 p = 1 := by simpa only [d179301, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22058 p hg
    simpa only [d179301, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22060 (p : Pattern) (guard : d179302 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179302, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21680 p hg
    simpa only [d179302, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179301 p = 1 := by simpa only [d179302, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22059 p hg
    simpa only [d179302, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22061 (p : Pattern) (guard : d179361 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179360 p = 1 := by simpa only [d179361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22057 p hg
    simpa only [d179361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179302 p = 1 := by simpa only [d179361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22060 p hg
    simpa only [d179361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22062 (p : Pattern) (guard : d179303 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179302 p = 1 := by simpa only [d179303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22060 p hg
    simpa only [d179303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21691 p hg
    simpa only [d179303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22063 (p : Pattern) (guard : d179362 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179361 p = 1 := by simpa only [d179362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22061 p hg
    simpa only [d179362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179303 p = 1 := by simpa only [d179362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22062 p hg
    simpa only [d179362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22064 (p : Pattern) (guard : d179363 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179362 p = 1 := by simpa only [d179363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22063 p hg
    simpa only [d179363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21691 p hg
    simpa only [d179363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22065 (p : Pattern) (guard : d179364 p = 1) : d48356 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179363 p = 1 := by simpa only [d179364, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22064 p hg
    simpa only [d179364, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179364, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21695 p hg
    simpa only [d179364, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22066 (p : Pattern) (guard : d179365 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179365, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21679 p hg
    simpa only [d179365, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179364 p = 1 := by simpa only [d179365, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22065 p hg
    simpa only [d179365, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22067 (p : Pattern) (guard : d179304 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179303 p = 1 := by simpa only [d179304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22062 p hg
    simpa only [d179304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21691 p hg
    simpa only [d179304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22068 (p : Pattern) (guard : d179305 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179304 p = 1 := by simpa only [d179305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22067 p hg
    simpa only [d179305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21691 p hg
    simpa only [d179305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22069 (p : Pattern) (guard : d179306 p = 1) : d48356 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179305 p = 1 := by simpa only [d179306, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22068 p hg
    simpa only [d179306, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179306, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21695 p hg
    simpa only [d179306, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22070 (p : Pattern) (guard : d179307 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179307, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21679 p hg
    simpa only [d179307, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179306 p = 1 := by simpa only [d179307, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22069 p hg
    simpa only [d179307, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22071 (p : Pattern) (guard : d179366 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179365 p = 1 := by simpa only [d179366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22066 p hg
    simpa only [d179366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179307 p = 1 := by simpa only [d179366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22070 p hg
    simpa only [d179366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22072 (p : Pattern) (guard : d179367 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179366 p = 1 := by simpa only [d179367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22071 p hg
    simpa only [d179367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22073 (p : Pattern) (guard : d179368 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179367 p = 1 := by simpa only [d179368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22072 p hg
    simpa only [d179368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22074 (p : Pattern) (guard : d179386 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179368 p = 1 := by simpa only [d179386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22073 p hg
    simpa only [d179386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22075 (p : Pattern) (guard : d179308 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179307 p = 1 := by simpa only [d179308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22070 p hg
    simpa only [d179308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22076 (p : Pattern) (guard : d179309 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179308 p = 1 := by simpa only [d179309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22075 p hg
    simpa only [d179309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22077 (p : Pattern) (guard : d179310 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179309 p = 1 := by simpa only [d179310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22076 p hg
    simpa only [d179310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22078 (p : Pattern) (guard : d179320 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179310 p = 1 := by simpa only [d179320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22077 p hg
    simpa only [d179320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22079 (p : Pattern) (guard : d179387 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179386 p = 1 := by simpa only [d179387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22074 p hg
    simpa only [d179387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179320 p = 1 := by simpa only [d179387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22078 p hg
    simpa only [d179387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22080 (p : Pattern) (guard : d179388 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179387 p = 1 := by simpa only [d179388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22079 p hg
    simpa only [d179388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22081 (p : Pattern) (guard : d179321 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179320 p = 1 := by simpa only [d179321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22078 p hg
    simpa only [d179321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22082 (p : Pattern) (guard : d179389 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179321 p = 1 := by simpa only [d179389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22081 p hg
    simpa only [d179389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22083 (p : Pattern) (guard : d179390 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179388 p = 1 := by simpa only [d179390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d179390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179389 p = 1 := by simpa only [d179390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22082 p hg
    simpa only [d179390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22084 (p : Pattern) (guard : d179400 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179390 p = 1 := by simpa only [d179400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22083 p hg
    simpa only [d179400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22085 (p : Pattern) (guard : d179401 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d179401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179400 p = 1 := by simpa only [d179401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22084 p hg
    simpa only [d179401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22086 (p : Pattern) (guard : d179402 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179402, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179402, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179401 p = 1 := by simpa only [d179402, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22085 p hg
    simpa only [d179402, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22087 (p : Pattern) (guard : d179403 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d179403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179402 p = 1 := by simpa only [d179403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22086 p hg
    simpa only [d179403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22088 (p : Pattern) (guard : d179404 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179403 p = 1 := by simpa only [d179404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22087 p hg
    simpa only [d179404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d179404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22089 (p : Pattern) (guard : d179405 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d179404 p = 1 := by simpa only [d179405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22088 p hg
    simpa only [d179405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d179405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22090 (p : Pattern) (guard : d179406 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d179405 p = 1 := by simpa only [d179406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22089 p hg
    simpa only [d179406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d179406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22091 (p : Pattern) (guard : d179407 p = 1) : d48359 p ≤ (1 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d179399 p = 1 := by simpa only [d179407, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22050 p hg
    simpa only [d179407, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179406 p = 1 := by simpa only [d179407, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22090 p hg
    simpa only [d179407, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22092 (p : Pattern) (guard : d179410 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare22093 (p : Pattern) (guard : d179411 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179410 p = 1 := by simpa only [d179411, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22092 p hg
    simpa only [d179411, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179411, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21719 p hg
    simpa only [d179411, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22094 (p : Pattern) (guard : d179412 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d179412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179411 p = 1 := by simpa only [d179412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22093 p hg
    simpa only [d179412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22095 (p : Pattern) (guard : d179413 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179412 p = 1 := by simpa only [d179413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22094 p hg
    simpa only [d179413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d179413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22096 (p : Pattern) (guard : d179414 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179413 p = 1 := by simpa only [d179414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22095 p hg
    simpa only [d179414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179268 p = 1 := by simpa only [d179414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21888 p hg
    simpa only [d179414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22097 (p : Pattern) (guard : d179415 p = 1) : d48362 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179415, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21716 p hg
    simpa only [d179415, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179414 p = 1 := by simpa only [d179415, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22096 p hg
    simpa only [d179415, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22098 (p : Pattern) (guard : d179416 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179416, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21715 p hg
    simpa only [d179416, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179415 p = 1 := by simpa only [d179416, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22097 p hg
    simpa only [d179416, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22099 (p : Pattern) (guard : d179417 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179268 p = 1 := by simpa only [d179417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21888 p hg
    simpa only [d179417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d179417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22100 (p : Pattern) (guard : d179418 p = 1) : d48362 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179418, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21716 p hg
    simpa only [d179418, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179417 p = 1 := by simpa only [d179418, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22099 p hg
    simpa only [d179418, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22101 (p : Pattern) (guard : d179419 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179419, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21715 p hg
    simpa only [d179419, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179418 p = 1 := by simpa only [d179419, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22100 p hg
    simpa only [d179419, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22102 (p : Pattern) (guard : d179420 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179416 p = 1 := by simpa only [d179420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22098 p hg
    simpa only [d179420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179419 p = 1 := by simpa only [d179420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22101 p hg
    simpa only [d179420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22103 (p : Pattern) (guard : d179421 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179419 p = 1 := by simpa only [d179421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22101 p hg
    simpa only [d179421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d179421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22104 (p : Pattern) (guard : d179422 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179420 p = 1 := by simpa only [d179422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22102 p hg
    simpa only [d179422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179421 p = 1 := by simpa only [d179422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22103 p hg
    simpa only [d179422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22105 (p : Pattern) (guard : d179423 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179422 p = 1 := by simpa only [d179423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22104 p hg
    simpa only [d179423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d179423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22106 (p : Pattern) (guard : d179424 p = 1) : d48365 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179423 p = 1 := by simpa only [d179424, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22105 p hg
    simpa only [d179424, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179424, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21730 p hg
    simpa only [d179424, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22107 (p : Pattern) (guard : d179425 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179425, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d179425, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179424 p = 1 := by simpa only [d179425, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22106 p hg
    simpa only [d179425, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22108 (p : Pattern) (guard : d179426 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179421 p = 1 := by simpa only [d179426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22103 p hg
    simpa only [d179426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d179426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22109 (p : Pattern) (guard : d179427 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179426 p = 1 := by simpa only [d179427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22108 p hg
    simpa only [d179427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d179427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22110 (p : Pattern) (guard : d179428 p = 1) : d48365 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179427 p = 1 := by simpa only [d179428, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22109 p hg
    simpa only [d179428, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179428, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21730 p hg
    simpa only [d179428, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22111 (p : Pattern) (guard : d179429 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179429, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d179429, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179428 p = 1 := by simpa only [d179429, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22110 p hg
    simpa only [d179429, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22112 (p : Pattern) (guard : d179430 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179425 p = 1 := by simpa only [d179430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22107 p hg
    simpa only [d179430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179429 p = 1 := by simpa only [d179430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22111 p hg
    simpa only [d179430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22113 (p : Pattern) (guard : d179431 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179430 p = 1 := by simpa only [d179431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22112 p hg
    simpa only [d179431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22114 (p : Pattern) (guard : d179432 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179431 p = 1 := by simpa only [d179432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22113 p hg
    simpa only [d179432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22115 (p : Pattern) (guard : d179433 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179432 p = 1 := by simpa only [d179433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22114 p hg
    simpa only [d179433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22116 (p : Pattern) (guard : d179434 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179429 p = 1 := by simpa only [d179434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22111 p hg
    simpa only [d179434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22117 (p : Pattern) (guard : d179435 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179434 p = 1 := by simpa only [d179435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22116 p hg
    simpa only [d179435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22118 (p : Pattern) (guard : d179436 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179435 p = 1 := by simpa only [d179436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22117 p hg
    simpa only [d179436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22119 (p : Pattern) (guard : d179437 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179436 p = 1 := by simpa only [d179437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22118 p hg
    simpa only [d179437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22120 (p : Pattern) (guard : d179438 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179433 p = 1 := by simpa only [d179438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22115 p hg
    simpa only [d179438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179437 p = 1 := by simpa only [d179438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22119 p hg
    simpa only [d179438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22121 (p : Pattern) (guard : d179439 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179438 p = 1 := by simpa only [d179439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22120 p hg
    simpa only [d179439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22122 (p : Pattern) (guard : d179440 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179437 p = 1 := by simpa only [d179440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22119 p hg
    simpa only [d179440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22123 (p : Pattern) (guard : d179441 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179440 p = 1 := by simpa only [d179441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22122 p hg
    simpa only [d179441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22124 (p : Pattern) (guard : d179442 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179439 p = 1 := by simpa only [d179442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22121 p hg
    simpa only [d179442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179441 p = 1 := by simpa only [d179442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22123 p hg
    simpa only [d179442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22125 (p : Pattern) (guard : d179443 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179442 p = 1 := by simpa only [d179443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22124 p hg
    simpa only [d179443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22126 (p : Pattern) (guard : d179444 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d179444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179443 p = 1 := by simpa only [d179444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22125 p hg
    simpa only [d179444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22127 (p : Pattern) (guard : d179445 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179445, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179445, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179444 p = 1 := by simpa only [d179445, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22126 p hg
    simpa only [d179445, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22128 (p : Pattern) (guard : d179446 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21713 p hg
    simpa only [d179446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179445 p = 1 := by simpa only [d179446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22127 p hg
    simpa only [d179446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22129 (p : Pattern) (guard : d179447 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179446 p = 1 := by simpa only [d179447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22128 p hg
    simpa only [d179447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21713 p hg
    simpa only [d179447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22130 (p : Pattern) (guard : d179448 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d179447 p = 1 := by simpa only [d179448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22129 p hg
    simpa only [d179448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21713 p hg
    simpa only [d179448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22131 (p : Pattern) (guard : d179449 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d179448 p = 1 := by simpa only [d179449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22130 p hg
    simpa only [d179449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21713 p hg
    simpa only [d179449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22132 (p : Pattern) (guard : d179450 p = 1) : d48387 p ≤ (1 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d179449 p = 1 := by simpa only [d179450, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22131 p hg
    simpa only [d179450, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179450, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21747 p hg
    simpa only [d179450, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22133 (p : Pattern) (guard : d179451 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d179407 p = 1 := by simpa only [d179451, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22091 p hg
    simpa only [d179451, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179450 p = 1 := by simpa only [d179451, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22132 p hg
    simpa only [d179451, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22134 (p : Pattern) (guard : d179452 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179451 p = 1 := by simpa only [d179452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22133 p hg
    simpa only [d179452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22135 (p : Pattern) (guard : d179453 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179452 p = 1 := by simpa only [d179453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22134 p hg
    simpa only [d179453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22136 (p : Pattern) (guard : d179454 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179453 p = 1 := by simpa only [d179454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22135 p hg
    simpa only [d179454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22137 (p : Pattern) (guard : d179455 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179454 p = 1 := by simpa only [d179455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22136 p hg
    simpa only [d179455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22138 (p : Pattern) (guard : d179456 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179455 p = 1 := by simpa only [d179456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22137 p hg
    simpa only [d179456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22139 (p : Pattern) (guard : d179457 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179456 p = 1 := by simpa only [d179457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22138 p hg
    simpa only [d179457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22140 (p : Pattern) (guard : d179458 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179457 p = 1 := by simpa only [d179458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22139 p hg
    simpa only [d179458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22141 (p : Pattern) (guard : d179459 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d179299 p = 1 := by simpa only [d179459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21919 p hg
    simpa only [d179459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179458 p = 1 := by simpa only [d179459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22140 p hg
    simpa only [d179459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22142 (p : Pattern) (guard : d179468 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare22143 (p : Pattern) (guard : d179469 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179468 p = 1 := by simpa only [d179469, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22142 p hg
    simpa only [d179469, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179469, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21624 p hg
    simpa only [d179469, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22144 (p : Pattern) (guard : d179470 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179469 p = 1 := by simpa only [d179470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22143 p hg
    simpa only [d179470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22145 (p : Pattern) (guard : d179471 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179470 p = 1 := by simpa only [d179471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22144 p hg
    simpa only [d179471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22146 (p : Pattern) (guard : d179480 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare22147 (p : Pattern) (guard : d179481 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179480 p = 1 := by simpa only [d179481, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22146 p hg
    simpa only [d179481, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179481, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21624 p hg
    simpa only [d179481, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22148 (p : Pattern) (guard : d179482 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179481 p = 1 := by simpa only [d179482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22147 p hg
    simpa only [d179482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22149 (p : Pattern) (guard : d179483 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179482 p = 1 := by simpa only [d179483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22148 p hg
    simpa only [d179483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22150 (p : Pattern) (guard : d179484 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179471 p = 1 := by simpa only [d179484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22145 p hg
    simpa only [d179484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179483 p = 1 := by simpa only [d179484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22149 p hg
    simpa only [d179484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22151 (p : Pattern) (guard : d179485 p = 1) : d48326 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179485, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21621 p hg
    simpa only [d179485, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179484 p = 1 := by simpa only [d179485, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22150 p hg
    simpa only [d179485, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22152 (p : Pattern) (guard : d179486 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179486, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21620 p hg
    simpa only [d179486, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179485 p = 1 := by simpa only [d179486, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22151 p hg
    simpa only [d179486, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22153 (p : Pattern) (guard : d179487 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179483 p = 1 := by simpa only [d179487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22149 p hg
    simpa only [d179487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22154 (p : Pattern) (guard : d179488 p = 1) : d48326 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179488, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21621 p hg
    simpa only [d179488, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179487 p = 1 := by simpa only [d179488, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22153 p hg
    simpa only [d179488, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22155 (p : Pattern) (guard : d179489 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179489, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21620 p hg
    simpa only [d179489, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179488 p = 1 := by simpa only [d179489, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22154 p hg
    simpa only [d179489, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22156 (p : Pattern) (guard : d179490 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179486 p = 1 := by simpa only [d179490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22152 p hg
    simpa only [d179490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179489 p = 1 := by simpa only [d179490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22155 p hg
    simpa only [d179490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22157 (p : Pattern) (guard : d179491 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179489 p = 1 := by simpa only [d179491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22155 p hg
    simpa only [d179491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21631 p hg
    simpa only [d179491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22158 (p : Pattern) (guard : d179492 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179490 p = 1 := by simpa only [d179492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22156 p hg
    simpa only [d179492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179491 p = 1 := by simpa only [d179492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22157 p hg
    simpa only [d179492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22159 (p : Pattern) (guard : d179493 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179492 p = 1 := by simpa only [d179493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22158 p hg
    simpa only [d179493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21631 p hg
    simpa only [d179493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22160 (p : Pattern) (guard : d179494 p = 1) : d48338 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179493 p = 1 := by simpa only [d179494, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22159 p hg
    simpa only [d179494, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179494, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d179494, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22161 (p : Pattern) (guard : d179495 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179495, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d179495, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179494 p = 1 := by simpa only [d179495, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22160 p hg
    simpa only [d179495, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22162 (p : Pattern) (guard : d179496 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179491 p = 1 := by simpa only [d179496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22157 p hg
    simpa only [d179496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21631 p hg
    simpa only [d179496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22163 (p : Pattern) (guard : d179497 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179496 p = 1 := by simpa only [d179497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22162 p hg
    simpa only [d179497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21631 p hg
    simpa only [d179497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22164 (p : Pattern) (guard : d179498 p = 1) : d48338 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179497 p = 1 := by simpa only [d179498, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22163 p hg
    simpa only [d179498, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179498, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d179498, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22165 (p : Pattern) (guard : d179499 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179499, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d179499, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179498 p = 1 := by simpa only [d179499, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22164 p hg
    simpa only [d179499, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22166 (p : Pattern) (guard : d179500 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179495 p = 1 := by simpa only [d179500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22161 p hg
    simpa only [d179500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179499 p = 1 := by simpa only [d179500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22165 p hg
    simpa only [d179500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22167 (p : Pattern) (guard : d179501 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179500 p = 1 := by simpa only [d179501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22166 p hg
    simpa only [d179501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22168 (p : Pattern) (guard : d179502 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179501 p = 1 := by simpa only [d179502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22167 p hg
    simpa only [d179502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22169 (p : Pattern) (guard : d179503 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179502 p = 1 := by simpa only [d179503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22168 p hg
    simpa only [d179503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22170 (p : Pattern) (guard : d179504 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179499 p = 1 := by simpa only [d179504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22165 p hg
    simpa only [d179504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22171 (p : Pattern) (guard : d179505 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179504 p = 1 := by simpa only [d179505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22170 p hg
    simpa only [d179505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22172 (p : Pattern) (guard : d179506 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179505 p = 1 := by simpa only [d179506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22171 p hg
    simpa only [d179506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22173 (p : Pattern) (guard : d179507 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179506 p = 1 := by simpa only [d179507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22172 p hg
    simpa only [d179507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22174 (p : Pattern) (guard : d179508 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179503 p = 1 := by simpa only [d179508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22169 p hg
    simpa only [d179508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179507 p = 1 := by simpa only [d179508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22173 p hg
    simpa only [d179508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22175 (p : Pattern) (guard : d179509 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179508 p = 1 := by simpa only [d179509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22174 p hg
    simpa only [d179509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22176 (p : Pattern) (guard : d179510 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179509 p = 1 := by simpa only [d179510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22175 p hg
    simpa only [d179510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22177 (p : Pattern) (guard : d179511 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179510 p = 1 := by simpa only [d179511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22176 p hg
    simpa only [d179511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22178 (p : Pattern) (guard : d179512 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179511 p = 1 := by simpa only [d179512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22177 p hg
    simpa only [d179512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22179 (p : Pattern) (guard : d179513 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179513, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179513, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179512 p = 1 := by simpa only [d179513, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22178 p hg
    simpa only [d179513, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22180 (p : Pattern) (guard : d179514 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d179514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179513 p = 1 := by simpa only [d179514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22179 p hg
    simpa only [d179514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22181 (p : Pattern) (guard : d179515 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179514 p = 1 := by simpa only [d179515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22180 p hg
    simpa only [d179515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d179515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22182 (p : Pattern) (guard : d179486 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179486, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21649 p hg
    simpa only [d179486, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179485 p = 1 := by simpa only [d179486, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22151 p hg
    simpa only [d179486, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22183 (p : Pattern) (guard : d179489 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179489, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21649 p hg
    simpa only [d179489, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179488 p = 1 := by simpa only [d179489, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22154 p hg
    simpa only [d179489, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22184 (p : Pattern) (guard : d179490 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179486 p = 1 := by simpa only [d179490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22182 p hg
    simpa only [d179490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179489 p = 1 := by simpa only [d179490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22183 p hg
    simpa only [d179490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22185 (p : Pattern) (guard : d179491 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179489 p = 1 := by simpa only [d179491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22183 p hg
    simpa only [d179491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21651 p hg
    simpa only [d179491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22186 (p : Pattern) (guard : d179492 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179490 p = 1 := by simpa only [d179492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22184 p hg
    simpa only [d179492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179491 p = 1 := by simpa only [d179492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22185 p hg
    simpa only [d179492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22187 (p : Pattern) (guard : d179493 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179492 p = 1 := by simpa only [d179493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22186 p hg
    simpa only [d179493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21651 p hg
    simpa only [d179493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22188 (p : Pattern) (guard : d179494 p = 1) : d48329 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179493 p = 1 := by simpa only [d179494, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22187 p hg
    simpa only [d179494, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179494, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d179494, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22189 (p : Pattern) (guard : d179495 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179495, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21648 p hg
    simpa only [d179495, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179494 p = 1 := by simpa only [d179495, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22188 p hg
    simpa only [d179495, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22190 (p : Pattern) (guard : d179496 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179491 p = 1 := by simpa only [d179496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22185 p hg
    simpa only [d179496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21651 p hg
    simpa only [d179496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22191 (p : Pattern) (guard : d179497 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179496 p = 1 := by simpa only [d179497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22190 p hg
    simpa only [d179497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21651 p hg
    simpa only [d179497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22192 (p : Pattern) (guard : d179498 p = 1) : d48329 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179497 p = 1 := by simpa only [d179498, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22191 p hg
    simpa only [d179498, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179498, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d179498, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22193 (p : Pattern) (guard : d179499 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179499, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21648 p hg
    simpa only [d179499, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179498 p = 1 := by simpa only [d179499, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22192 p hg
    simpa only [d179499, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22194 (p : Pattern) (guard : d179500 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179495 p = 1 := by simpa only [d179500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22189 p hg
    simpa only [d179500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179499 p = 1 := by simpa only [d179500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22193 p hg
    simpa only [d179500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22195 (p : Pattern) (guard : d179501 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179500 p = 1 := by simpa only [d179501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22194 p hg
    simpa only [d179501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22196 (p : Pattern) (guard : d179502 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179501 p = 1 := by simpa only [d179502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22195 p hg
    simpa only [d179502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22197 (p : Pattern) (guard : d179503 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179502 p = 1 := by simpa only [d179503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22196 p hg
    simpa only [d179503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22198 (p : Pattern) (guard : d179504 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179499 p = 1 := by simpa only [d179504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22193 p hg
    simpa only [d179504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22199 (p : Pattern) (guard : d179505 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179504 p = 1 := by simpa only [d179505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22198 p hg
    simpa only [d179505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22200 (p : Pattern) (guard : d179506 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179505 p = 1 := by simpa only [d179506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22199 p hg
    simpa only [d179506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22201 (p : Pattern) (guard : d179507 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179506 p = 1 := by simpa only [d179507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22200 p hg
    simpa only [d179507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22202 (p : Pattern) (guard : d179508 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179503 p = 1 := by simpa only [d179508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22197 p hg
    simpa only [d179508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179507 p = 1 := by simpa only [d179508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22201 p hg
    simpa only [d179508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22203 (p : Pattern) (guard : d179509 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179508 p = 1 := by simpa only [d179509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22202 p hg
    simpa only [d179509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22204 (p : Pattern) (guard : d179510 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179509 p = 1 := by simpa only [d179510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22203 p hg
    simpa only [d179510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22205 (p : Pattern) (guard : d179511 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179510 p = 1 := by simpa only [d179511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22204 p hg
    simpa only [d179511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22206 (p : Pattern) (guard : d179512 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179511 p = 1 := by simpa only [d179512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22205 p hg
    simpa only [d179512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22207 (p : Pattern) (guard : d179516 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179502 p = 1 := by simpa only [d179516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22168 p hg
    simpa only [d179516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22208 (p : Pattern) (guard : d179517 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179506 p = 1 := by simpa only [d179517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22172 p hg
    simpa only [d179517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22209 (p : Pattern) (guard : d179518 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179516 p = 1 := by simpa only [d179518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22207 p hg
    simpa only [d179518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179517 p = 1 := by simpa only [d179518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22208 p hg
    simpa only [d179518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22210 (p : Pattern) (guard : d179519 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179518 p = 1 := by simpa only [d179519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22209 p hg
    simpa only [d179519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22211 (p : Pattern) (guard : d179520 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179519 p = 1 := by simpa only [d179520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22210 p hg
    simpa only [d179520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22212 (p : Pattern) (guard : d179521 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179520 p = 1 := by simpa only [d179521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22211 p hg
    simpa only [d179521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22213 (p : Pattern) (guard : d179522 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179521 p = 1 := by simpa only [d179522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22212 p hg
    simpa only [d179522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22214 (p : Pattern) (guard : d179523 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d179512 p = 1 := by simpa only [d179523, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22206 p hg
    simpa only [d179523, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179522 p = 1 := by simpa only [d179523, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22213 p hg
    simpa only [d179523, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22215 (p : Pattern) (guard : d179524 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d179513 p = 1 := by simpa only [d179524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22179 p hg
    simpa only [d179524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179523 p = 1 := by simpa only [d179524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22214 p hg
    simpa only [d179524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22216 (p : Pattern) (guard : d179525 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179524 p = 1 := by simpa only [d179525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22215 p hg
    simpa only [d179525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d179525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22217 (p : Pattern) (guard : d179526 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d179515 p = 1 := by simpa only [d179526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22181 p hg
    simpa only [d179526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179525 p = 1 := by simpa only [d179526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22216 p hg
    simpa only [d179526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22218 (p : Pattern) (guard : d179527 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179501 p = 1 := by simpa only [d179527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22167 p hg
    simpa only [d179527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22219 (p : Pattern) (guard : d179528 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179527 p = 1 := by simpa only [d179528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22218 p hg
    simpa only [d179528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22220 (p : Pattern) (guard : d179529 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179505 p = 1 := by simpa only [d179529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22171 p hg
    simpa only [d179529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22221 (p : Pattern) (guard : d179530 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179529 p = 1 := by simpa only [d179530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22220 p hg
    simpa only [d179530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22222 (p : Pattern) (guard : d179531 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179528 p = 1 := by simpa only [d179531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22219 p hg
    simpa only [d179531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179530 p = 1 := by simpa only [d179531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22221 p hg
    simpa only [d179531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22223 (p : Pattern) (guard : d179532 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179531 p = 1 := by simpa only [d179532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22222 p hg
    simpa only [d179532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22224 (p : Pattern) (guard : d179533 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179532 p = 1 := by simpa only [d179533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22223 p hg
    simpa only [d179533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22225 (p : Pattern) (guard : d179534 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179533 p = 1 := by simpa only [d179534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22224 p hg
    simpa only [d179534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22226 (p : Pattern) (guard : d179535 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179500 p = 1 := by simpa only [d179535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22166 p hg
    simpa only [d179535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22227 (p : Pattern) (guard : d179536 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179535 p = 1 := by simpa only [d179536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22226 p hg
    simpa only [d179536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22228 (p : Pattern) (guard : d179537 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179536 p = 1 := by simpa only [d179537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22227 p hg
    simpa only [d179537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22229 (p : Pattern) (guard : d179538 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179504 p = 1 := by simpa only [d179538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22170 p hg
    simpa only [d179538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22230 (p : Pattern) (guard : d179539 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179538 p = 1 := by simpa only [d179539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22229 p hg
    simpa only [d179539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22231 (p : Pattern) (guard : d179540 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179539 p = 1 := by simpa only [d179540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22230 p hg
    simpa only [d179540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22232 (p : Pattern) (guard : d179541 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179537 p = 1 := by simpa only [d179541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22228 p hg
    simpa only [d179541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179540 p = 1 := by simpa only [d179541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22231 p hg
    simpa only [d179541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22233 (p : Pattern) (guard : d179542 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179541 p = 1 := by simpa only [d179542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22232 p hg
    simpa only [d179542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22234 (p : Pattern) (guard : d179543 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179542 p = 1 := by simpa only [d179543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22233 p hg
    simpa only [d179543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22235 (p : Pattern) (guard : d179550 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare22236 (p : Pattern) (guard : d179551 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179550 p = 1 := by simpa only [d179551, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22235 p hg
    simpa only [d179551, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179551, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21624 p hg
    simpa only [d179551, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22237 (p : Pattern) (guard : d179552 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179551 p = 1 := by simpa only [d179552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22236 p hg
    simpa only [d179552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22238 (p : Pattern) (guard : d179553 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179552 p = 1 := by simpa only [d179553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22237 p hg
    simpa only [d179553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22239 (p : Pattern) (guard : d179554 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179553 p = 1 := by simpa only [d179554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22238 p hg
    simpa only [d179554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179471 p = 1 := by simpa only [d179554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22145 p hg
    simpa only [d179554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22240 (p : Pattern) (guard : d179555 p = 1) : d48326 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179555, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21621 p hg
    simpa only [d179555, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179554 p = 1 := by simpa only [d179555, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22239 p hg
    simpa only [d179555, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22241 (p : Pattern) (guard : d179556 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179556, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21620 p hg
    simpa only [d179556, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179555 p = 1 := by simpa only [d179556, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22240 p hg
    simpa only [d179556, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22242 (p : Pattern) (guard : d179557 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179471 p = 1 := by simpa only [d179557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22145 p hg
    simpa only [d179557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22243 (p : Pattern) (guard : d179558 p = 1) : d48326 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179558, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21621 p hg
    simpa only [d179558, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179557 p = 1 := by simpa only [d179558, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22242 p hg
    simpa only [d179558, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22244 (p : Pattern) (guard : d179559 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179559, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21620 p hg
    simpa only [d179559, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179558 p = 1 := by simpa only [d179559, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22243 p hg
    simpa only [d179559, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22245 (p : Pattern) (guard : d179560 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179556 p = 1 := by simpa only [d179560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22241 p hg
    simpa only [d179560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179559 p = 1 := by simpa only [d179560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22244 p hg
    simpa only [d179560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22246 (p : Pattern) (guard : d179561 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179560 p = 1 := by simpa only [d179561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22245 p hg
    simpa only [d179561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179490 p = 1 := by simpa only [d179561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22156 p hg
    simpa only [d179561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22247 (p : Pattern) (guard : d179562 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179561 p = 1 := by simpa only [d179562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22246 p hg
    simpa only [d179562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21631 p hg
    simpa only [d179562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22248 (p : Pattern) (guard : d179563 p = 1) : d48338 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179562 p = 1 := by simpa only [d179563, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22247 p hg
    simpa only [d179563, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179563, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d179563, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22249 (p : Pattern) (guard : d179564 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179564, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d179564, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179563 p = 1 := by simpa only [d179564, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22248 p hg
    simpa only [d179564, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
