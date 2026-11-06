import NetHack.Soko22Hazard87.Compare075
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare19000 (p : Pattern) (guard : d16476 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16476, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16476, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16475 p = 1 := by simpa only [d16476, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18999 p hg
    simpa only [d16476, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19001 (p : Pattern) (guard : d16477 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d16477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16476 p = 1 := by simpa only [d16477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19000 p hg
    simpa only [d16477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19002 (p : Pattern) (guard : d16478 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d16477 p = 1 := by simpa only [d16478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19001 p hg
    simpa only [d16478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d16478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19003 (p : Pattern) (guard : d16446 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16446, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d16446, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16445 p = 1 := by simpa only [d16446, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18954 p hg
    simpa only [d16446, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19004 (p : Pattern) (guard : d16449 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16449, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d16449, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16448 p = 1 := by simpa only [d16449, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18970 p hg
    simpa only [d16449, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19005 (p : Pattern) (guard : d16450 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16446 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19003 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16449 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19004 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19006 (p : Pattern) (guard : d16453 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16453, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d16453, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16452 p = 1 := by simpa only [d16453, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18976 p hg
    simpa only [d16453, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19007 (p : Pattern) (guard : d16454 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16453 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19006 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19008 (p : Pattern) (guard : d16455 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16450 p = 1 := by simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19005 p hg
    simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16454 p = 1 := by simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19007 p hg
    simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19009 (p : Pattern) (guard : d16456 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16455 p = 1 := by simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19008 p hg
    simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19010 (p : Pattern) (guard : d16457 p = 1) : d48329 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16456 p = 1 := by simpa only [d16457, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19009 p hg
    simpa only [d16457, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16457, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16457, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19011 (p : Pattern) (guard : d16458 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16458, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17906 p hg
    simpa only [d16458, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16457 p = 1 := by simpa only [d16458, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19010 p hg
    simpa only [d16458, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19012 (p : Pattern) (guard : d16459 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16454 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19007 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19013 (p : Pattern) (guard : d16460 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16459 p = 1 := by simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19012 p hg
    simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19014 (p : Pattern) (guard : d16461 p = 1) : d48329 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16460 p = 1 := by simpa only [d16461, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19013 p hg
    simpa only [d16461, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16461, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16461, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19015 (p : Pattern) (guard : d16462 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16462, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17906 p hg
    simpa only [d16462, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16461 p = 1 := by simpa only [d16462, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19014 p hg
    simpa only [d16462, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19016 (p : Pattern) (guard : d16463 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16458 p = 1 := by simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19011 p hg
    simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16462 p = 1 := by simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19015 p hg
    simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19017 (p : Pattern) (guard : d16464 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16463 p = 1 := by simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19016 p hg
    simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19018 (p : Pattern) (guard : d16465 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16464 p = 1 := by simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19017 p hg
    simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19019 (p : Pattern) (guard : d16466 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16465 p = 1 := by simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19018 p hg
    simpa only [d16466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19020 (p : Pattern) (guard : d16467 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16462 p = 1 := by simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19015 p hg
    simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19021 (p : Pattern) (guard : d16468 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16467 p = 1 := by simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19020 p hg
    simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19022 (p : Pattern) (guard : d16469 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16468 p = 1 := by simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19021 p hg
    simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19023 (p : Pattern) (guard : d16470 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16469 p = 1 := by simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19022 p hg
    simpa only [d16470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19024 (p : Pattern) (guard : d16471 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16466 p = 1 := by simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19019 p hg
    simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16470 p = 1 := by simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19023 p hg
    simpa only [d16471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19025 (p : Pattern) (guard : d16472 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16471 p = 1 := by simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19024 p hg
    simpa only [d16472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19026 (p : Pattern) (guard : d16473 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16472 p = 1 := by simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19025 p hg
    simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19027 (p : Pattern) (guard : d16474 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16473 p = 1 := by simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19026 p hg
    simpa only [d16474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19028 (p : Pattern) (guard : d16475 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16474 p = 1 := by simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19027 p hg
    simpa only [d16475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19029 (p : Pattern) (guard : d16479 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16465 p = 1 := by simpa only [d16479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18989 p hg
    simpa only [d16479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19030 (p : Pattern) (guard : d16480 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16469 p = 1 := by simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18993 p hg
    simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19031 (p : Pattern) (guard : d16481 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16479 p = 1 := by simpa only [d16481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19029 p hg
    simpa only [d16481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16480 p = 1 := by simpa only [d16481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19030 p hg
    simpa only [d16481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19032 (p : Pattern) (guard : d16482 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16481 p = 1 := by simpa only [d16482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19031 p hg
    simpa only [d16482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19033 (p : Pattern) (guard : d16483 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16482 p = 1 := by simpa only [d16483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19032 p hg
    simpa only [d16483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19034 (p : Pattern) (guard : d16484 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16483 p = 1 := by simpa only [d16484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19033 p hg
    simpa only [d16484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19035 (p : Pattern) (guard : d16485 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16484 p = 1 := by simpa only [d16485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19034 p hg
    simpa only [d16485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19036 (p : Pattern) (guard : d16486 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16475 p = 1 := by simpa only [d16486, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19028 p hg
    simpa only [d16486, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16485 p = 1 := by simpa only [d16486, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19035 p hg
    simpa only [d16486, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19037 (p : Pattern) (guard : d16487 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d16476 p = 1 := by simpa only [d16487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19000 p hg
    simpa only [d16487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16486 p = 1 := by simpa only [d16487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19036 p hg
    simpa only [d16487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19038 (p : Pattern) (guard : d16488 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d16487 p = 1 := by simpa only [d16488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19037 p hg
    simpa only [d16488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d16488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19039 (p : Pattern) (guard : d16489 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 51 with
  | false =>
    have hg : d16478 p = 1 := by simpa only [d16489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19002 p hg
    simpa only [d16489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16488 p = 1 := by simpa only [d16489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19038 p hg
    simpa only [d16489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19040 (p : Pattern) (guard : d16490 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16464 p = 1 := by simpa only [d16490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18988 p hg
    simpa only [d16490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19041 (p : Pattern) (guard : d16491 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16490 p = 1 := by simpa only [d16491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19040 p hg
    simpa only [d16491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19042 (p : Pattern) (guard : d16492 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16468 p = 1 := by simpa only [d16492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18992 p hg
    simpa only [d16492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19043 (p : Pattern) (guard : d16493 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16492 p = 1 := by simpa only [d16493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19042 p hg
    simpa only [d16493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19044 (p : Pattern) (guard : d16494 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16491 p = 1 := by simpa only [d16494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19041 p hg
    simpa only [d16494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16493 p = 1 := by simpa only [d16494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19043 p hg
    simpa only [d16494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19045 (p : Pattern) (guard : d16495 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16494 p = 1 := by simpa only [d16495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19044 p hg
    simpa only [d16495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19046 (p : Pattern) (guard : d16496 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16495 p = 1 := by simpa only [d16496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19045 p hg
    simpa only [d16496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19047 (p : Pattern) (guard : d16497 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16496 p = 1 := by simpa only [d16497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19046 p hg
    simpa only [d16497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19048 (p : Pattern) (guard : d16498 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16463 p = 1 := by simpa only [d16498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18987 p hg
    simpa only [d16498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19049 (p : Pattern) (guard : d16499 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16498 p = 1 := by simpa only [d16499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19048 p hg
    simpa only [d16499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19050 (p : Pattern) (guard : d16500 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16499 p = 1 := by simpa only [d16500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19049 p hg
    simpa only [d16500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19051 (p : Pattern) (guard : d16501 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16467 p = 1 := by simpa only [d16501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18991 p hg
    simpa only [d16501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19052 (p : Pattern) (guard : d16502 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16501 p = 1 := by simpa only [d16502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19051 p hg
    simpa only [d16502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19053 (p : Pattern) (guard : d16503 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16502 p = 1 := by simpa only [d16503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19052 p hg
    simpa only [d16503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19054 (p : Pattern) (guard : d16504 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16500 p = 1 := by simpa only [d16504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19050 p hg
    simpa only [d16504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16503 p = 1 := by simpa only [d16504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19053 p hg
    simpa only [d16504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19055 (p : Pattern) (guard : d16505 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16504 p = 1 := by simpa only [d16505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19054 p hg
    simpa only [d16505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19056 (p : Pattern) (guard : d16506 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16505 p = 1 := by simpa only [d16506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19055 p hg
    simpa only [d16506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19057 (p : Pattern) (guard : d1209 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19058 (p : Pattern) (guard : d1210 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1209 p = 1 := by simpa only [d1210, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19057 p hg
    simpa only [d1210, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1210, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d1210, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19059 (p : Pattern) (guard : d1211 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1210 p = 1 := by simpa only [d1211, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19058 p hg
    simpa only [d1211, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1211, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d1211, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19060 (p : Pattern) (guard : d1212 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1212, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d1212, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1211 p = 1 := by simpa only [d1212, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19059 p hg
    simpa only [d1212, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19061 (p : Pattern) (guard : d1213 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1212 p = 1 := by simpa only [d1213, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19060 p hg
    simpa only [d1213, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1213, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d1213, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19062 (p : Pattern) (guard : d9752 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19063 (p : Pattern) (guard : d9753 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9752 p = 1 := by simpa only [d9753, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19062 p hg
    simpa only [d9753, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9753, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d9753, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19064 (p : Pattern) (guard : d9755 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9753 p = 1 := by simpa only [d9755, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19063 p hg
    simpa only [d9755, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9755, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d9755, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19065 (p : Pattern) (guard : d16507 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16507, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d16507, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9755 p = 1 := by simpa only [d16507, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19064 p hg
    simpa only [d16507, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19066 (p : Pattern) (guard : d16508 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16507 p = 1 := by simpa only [d16508, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19065 p hg
    simpa only [d16508, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16508, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d16508, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19067 (p : Pattern) (guard : d16509 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1213 p = 1 := by simpa only [d16509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19061 p hg
    simpa only [d16509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16508 p = 1 := by simpa only [d16509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19066 p hg
    simpa only [d16509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19068 (p : Pattern) (guard : d9762 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19069 (p : Pattern) (guard : d9763 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9762 p = 1 := by simpa only [d9763, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19068 p hg
    simpa only [d9763, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9763, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d9763, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19070 (p : Pattern) (guard : d9765 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9763 p = 1 := by simpa only [d9765, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19069 p hg
    simpa only [d9765, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9765, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d9765, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19071 (p : Pattern) (guard : d14836 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14836, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d14836, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9765 p = 1 := by simpa only [d14836, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19070 p hg
    simpa only [d14836, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19072 (p : Pattern) (guard : d14837 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14836 p = 1 := by simpa only [d14837, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19071 p hg
    simpa only [d14837, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14837, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d14837, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19073 (p : Pattern) (guard : d16510 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14837 p = 1 := by simpa only [d16510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19072 p hg
    simpa only [d16510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14759 p = 1 := by simpa only [d16510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18932 p hg
    simpa only [d16510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19074 (p : Pattern) (guard : d16511 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16509 p = 1 := by simpa only [d16511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19067 p hg
    simpa only [d16511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16510 p = 1 := by simpa only [d16511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19073 p hg
    simpa only [d16511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19075 (p : Pattern) (guard : d16512 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16511 p = 1 := by simpa only [d16512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19074 p hg
    simpa only [d16512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16442 p = 1 := by simpa only [d16512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18939 p hg
    simpa only [d16512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19076 (p : Pattern) (guard : d16513 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16513, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d16513, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16512 p = 1 := by simpa only [d16513, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19075 p hg
    simpa only [d16513, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19077 (p : Pattern) (guard : d16514 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16514, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d16514, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16513 p = 1 := by simpa only [d16514, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19076 p hg
    simpa only [d16514, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19078 (p : Pattern) (guard : d9813 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19079 (p : Pattern) (guard : d9814 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9813 p = 1 := by simpa only [d9814, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19078 p hg
    simpa only [d9814, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9814, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d9814, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19080 (p : Pattern) (guard : d9816 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9814 p = 1 := by simpa only [d9816, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19079 p hg
    simpa only [d9816, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9816, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d9816, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19081 (p : Pattern) (guard : d13022 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d13022, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d13022, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9816 p = 1 := by simpa only [d13022, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19080 p hg
    simpa only [d13022, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19082 (p : Pattern) (guard : d13023 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13022 p = 1 := by simpa only [d13023, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19081 p hg
    simpa only [d13023, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13023, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d13023, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19083 (p : Pattern) (guard : d16515 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13023 p = 1 := by simpa only [d16515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19082 p hg
    simpa only [d16515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14764 p = 1 := by simpa only [d16515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18937 p hg
    simpa only [d16515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19084 (p : Pattern) (guard : d16516 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16515 p = 1 := by simpa only [d16516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19083 p hg
    simpa only [d16516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14765 p = 1 := by simpa only [d16516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18951 p hg
    simpa only [d16516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19085 (p : Pattern) (guard : d16517 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16442 p = 1 := by simpa only [d16517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18939 p hg
    simpa only [d16517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16516 p = 1 := by simpa only [d16517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19084 p hg
    simpa only [d16517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19086 (p : Pattern) (guard : d16518 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16518, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d16518, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16517 p = 1 := by simpa only [d16518, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19085 p hg
    simpa only [d16518, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19087 (p : Pattern) (guard : d16519 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16519, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d16519, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16518 p = 1 := by simpa only [d16519, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19086 p hg
    simpa only [d16519, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19088 (p : Pattern) (guard : d16520 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16514 p = 1 := by simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19077 p hg
    simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16519 p = 1 := by simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19087 p hg
    simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19089 (p : Pattern) (guard : d16521 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16520 p = 1 := by simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19088 p hg
    simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16450 p = 1 := by simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18972 p hg
    simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19090 (p : Pattern) (guard : d16522 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16521 p = 1 := by simpa only [d16522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19089 p hg
    simpa only [d16522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d16522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19091 (p : Pattern) (guard : d16523 p = 1) : d48338 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16522 p = 1 := by simpa only [d16523, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19090 p hg
    simpa only [d16523, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16523, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16523, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19092 (p : Pattern) (guard : d16524 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16524, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17871 p hg
    simpa only [d16524, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16523 p = 1 := by simpa only [d16524, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19091 p hg
    simpa only [d16524, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19093 (p : Pattern) (guard : d16525 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16449 p = 1 := by simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18971 p hg
    simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19094 (p : Pattern) (guard : d16526 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16450 p = 1 := by simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18972 p hg
    simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16525 p = 1 := by simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19093 p hg
    simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19095 (p : Pattern) (guard : d16527 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16526 p = 1 := by simpa only [d16527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19094 p hg
    simpa only [d16527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d16527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19096 (p : Pattern) (guard : d16528 p = 1) : d48338 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16527 p = 1 := by simpa only [d16528, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19095 p hg
    simpa only [d16528, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16528, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16528, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19097 (p : Pattern) (guard : d16529 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16529, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17871 p hg
    simpa only [d16529, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16528 p = 1 := by simpa only [d16529, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19096 p hg
    simpa only [d16529, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19098 (p : Pattern) (guard : d16530 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16524 p = 1 := by simpa only [d16530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19092 p hg
    simpa only [d16530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16529 p = 1 := by simpa only [d16530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19097 p hg
    simpa only [d16530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19099 (p : Pattern) (guard : d16531 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16530 p = 1 := by simpa only [d16531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19098 p hg
    simpa only [d16531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19100 (p : Pattern) (guard : d16532 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16531 p = 1 := by simpa only [d16532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19099 p hg
    simpa only [d16532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19101 (p : Pattern) (guard : d16533 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16532 p = 1 := by simpa only [d16533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19100 p hg
    simpa only [d16533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19102 (p : Pattern) (guard : d16534 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16529 p = 1 := by simpa only [d16534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19097 p hg
    simpa only [d16534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16462 p = 1 := by simpa only [d16534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18986 p hg
    simpa only [d16534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19103 (p : Pattern) (guard : d16535 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16534 p = 1 := by simpa only [d16535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19102 p hg
    simpa only [d16535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19104 (p : Pattern) (guard : d16536 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16535 p = 1 := by simpa only [d16536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19103 p hg
    simpa only [d16536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19105 (p : Pattern) (guard : d16537 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16536 p = 1 := by simpa only [d16537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19104 p hg
    simpa only [d16537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19106 (p : Pattern) (guard : d16538 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16533 p = 1 := by simpa only [d16538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19101 p hg
    simpa only [d16538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16537 p = 1 := by simpa only [d16538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19105 p hg
    simpa only [d16538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19107 (p : Pattern) (guard : d128311 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16538 p = 1 := by simpa only [d128311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19106 p hg
    simpa only [d128311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d128311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19108 (p : Pattern) (guard : d12961 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1127 p = 1 := by simpa only [d12961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18973 p hg
    simpa only [d12961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17883 p hg
    simpa only [d12961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19109 (p : Pattern) (guard : d16574 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18952 p hg
    simpa only [d16574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12961 p = 1 := by simpa only [d16574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19108 p hg
    simpa only [d16574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19110 (p : Pattern) (guard : d16575 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16575, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d16575, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16574 p = 1 := by simpa only [d16575, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19109 p hg
    simpa only [d16575, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19111 (p : Pattern) (guard : d16576 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16576, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d16576, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16575 p = 1 := by simpa only [d16576, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19110 p hg
    simpa only [d16576, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19112 (p : Pattern) (guard : d16577 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16576 p = 1 := by simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19111 p hg
    simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19113 (p : Pattern) (guard : d16578 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16450 p = 1 := by simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18972 p hg
    simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16577 p = 1 := by simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19112 p hg
    simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19114 (p : Pattern) (guard : d16579 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16578 p = 1 := by simpa only [d16579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19113 p hg
    simpa only [d16579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d16579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19115 (p : Pattern) (guard : d16580 p = 1) : d48338 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16579 p = 1 := by simpa only [d16580, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19114 p hg
    simpa only [d16580, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16580, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16580, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19116 (p : Pattern) (guard : d16581 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16581, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17871 p hg
    simpa only [d16581, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16580 p = 1 := by simpa only [d16581, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19115 p hg
    simpa only [d16581, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19117 (p : Pattern) (guard : d16582 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16581 p = 1 := by simpa only [d16582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19116 p hg
    simpa only [d16582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19118 (p : Pattern) (guard : d16583 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16582 p = 1 := by simpa only [d16583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19117 p hg
    simpa only [d16583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19119 (p : Pattern) (guard : d16584 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16583 p = 1 := by simpa only [d16584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19118 p hg
    simpa only [d16584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19120 (p : Pattern) (guard : d16585 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16584 p = 1 := by simpa only [d16585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19119 p hg
    simpa only [d16585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19121 (p : Pattern) (guard : d16586 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16585 p = 1 := by simpa only [d16586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19120 p hg
    simpa only [d16586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19122 (p : Pattern) (guard : d16587 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16586 p = 1 := by simpa only [d16587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19121 p hg
    simpa only [d16587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19123 (p : Pattern) (guard : d128312 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128311 p = 1 := by simpa only [d128312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19107 p hg
    simpa only [d128312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16587 p = 1 := by simpa only [d128312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19122 p hg
    simpa only [d128312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19124 (p : Pattern) (guard : d128313 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d16506 p = 1 := by simpa only [d128313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19056 p hg
    simpa only [d128313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128312 p = 1 := by simpa only [d128313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19123 p hg
    simpa only [d128313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19125 (p : Pattern) (guard : d128314 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d16497 p = 1 := by simpa only [d128314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19047 p hg
    simpa only [d128314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128313 p = 1 := by simpa only [d128314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19124 p hg
    simpa only [d128314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19126 (p : Pattern) (guard : d128315 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128315, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d128315, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128314 p = 1 := by simpa only [d128315, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19125 p hg
    simpa only [d128315, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19127 (p : Pattern) (guard : d16490 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16464 p = 1 := by simpa only [d16490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19017 p hg
    simpa only [d16490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19128 (p : Pattern) (guard : d16491 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16490 p = 1 := by simpa only [d16491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19127 p hg
    simpa only [d16491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19129 (p : Pattern) (guard : d16492 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16468 p = 1 := by simpa only [d16492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19021 p hg
    simpa only [d16492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19130 (p : Pattern) (guard : d16493 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16492 p = 1 := by simpa only [d16493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19129 p hg
    simpa only [d16493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19131 (p : Pattern) (guard : d16494 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16491 p = 1 := by simpa only [d16494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19128 p hg
    simpa only [d16494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16493 p = 1 := by simpa only [d16494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19130 p hg
    simpa only [d16494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19132 (p : Pattern) (guard : d16495 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16494 p = 1 := by simpa only [d16495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19131 p hg
    simpa only [d16495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19133 (p : Pattern) (guard : d16496 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16495 p = 1 := by simpa only [d16496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19132 p hg
    simpa only [d16496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19134 (p : Pattern) (guard : d16497 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16496 p = 1 := by simpa only [d16497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19133 p hg
    simpa only [d16497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19135 (p : Pattern) (guard : d16498 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16463 p = 1 := by simpa only [d16498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19016 p hg
    simpa only [d16498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19136 (p : Pattern) (guard : d16499 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16498 p = 1 := by simpa only [d16499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19135 p hg
    simpa only [d16499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19137 (p : Pattern) (guard : d16500 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16499 p = 1 := by simpa only [d16500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19136 p hg
    simpa only [d16500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19138 (p : Pattern) (guard : d16501 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16467 p = 1 := by simpa only [d16501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19020 p hg
    simpa only [d16501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19139 (p : Pattern) (guard : d16502 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16501 p = 1 := by simpa only [d16502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19138 p hg
    simpa only [d16502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19140 (p : Pattern) (guard : d16503 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16502 p = 1 := by simpa only [d16503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19139 p hg
    simpa only [d16503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19141 (p : Pattern) (guard : d16504 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16500 p = 1 := by simpa only [d16504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19137 p hg
    simpa only [d16504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16503 p = 1 := by simpa only [d16504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19140 p hg
    simpa only [d16504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19142 (p : Pattern) (guard : d16505 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16504 p = 1 := by simpa only [d16505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19141 p hg
    simpa only [d16505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19143 (p : Pattern) (guard : d16506 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16505 p = 1 := by simpa only [d16506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19142 p hg
    simpa only [d16506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19144 (p : Pattern) (guard : d16514 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16514, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d16514, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16513 p = 1 := by simpa only [d16514, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19076 p hg
    simpa only [d16514, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19145 (p : Pattern) (guard : d16519 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16519, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d16519, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16518 p = 1 := by simpa only [d16519, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19086 p hg
    simpa only [d16519, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19146 (p : Pattern) (guard : d16520 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16514 p = 1 := by simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19144 p hg
    simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16519 p = 1 := by simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19145 p hg
    simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19147 (p : Pattern) (guard : d16521 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16520 p = 1 := by simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19146 p hg
    simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16450 p = 1 := by simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19005 p hg
    simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19148 (p : Pattern) (guard : d16522 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16521 p = 1 := by simpa only [d16522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19147 p hg
    simpa only [d16522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d16522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19149 (p : Pattern) (guard : d16523 p = 1) : d48329 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16522 p = 1 := by simpa only [d16523, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19148 p hg
    simpa only [d16523, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16523, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16523, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19150 (p : Pattern) (guard : d16524 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16524, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17906 p hg
    simpa only [d16524, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16523 p = 1 := by simpa only [d16524, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19149 p hg
    simpa only [d16524, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19151 (p : Pattern) (guard : d16525 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16449 p = 1 := by simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19004 p hg
    simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19152 (p : Pattern) (guard : d16526 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16450 p = 1 := by simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19005 p hg
    simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16525 p = 1 := by simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19151 p hg
    simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19153 (p : Pattern) (guard : d16527 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16526 p = 1 := by simpa only [d16527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19152 p hg
    simpa only [d16527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d16527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19154 (p : Pattern) (guard : d16528 p = 1) : d48329 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16527 p = 1 := by simpa only [d16528, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19153 p hg
    simpa only [d16528, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16528, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16528, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19155 (p : Pattern) (guard : d16529 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16529, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17906 p hg
    simpa only [d16529, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16528 p = 1 := by simpa only [d16529, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19154 p hg
    simpa only [d16529, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19156 (p : Pattern) (guard : d16530 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16524 p = 1 := by simpa only [d16530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19150 p hg
    simpa only [d16530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16529 p = 1 := by simpa only [d16530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19155 p hg
    simpa only [d16530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19157 (p : Pattern) (guard : d16531 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16530 p = 1 := by simpa only [d16531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19156 p hg
    simpa only [d16531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19158 (p : Pattern) (guard : d16532 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16531 p = 1 := by simpa only [d16532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19157 p hg
    simpa only [d16532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19159 (p : Pattern) (guard : d16533 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16532 p = 1 := by simpa only [d16533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19158 p hg
    simpa only [d16533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19160 (p : Pattern) (guard : d16534 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16529 p = 1 := by simpa only [d16534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19155 p hg
    simpa only [d16534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16462 p = 1 := by simpa only [d16534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19015 p hg
    simpa only [d16534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19161 (p : Pattern) (guard : d16535 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16534 p = 1 := by simpa only [d16535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19160 p hg
    simpa only [d16535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19162 (p : Pattern) (guard : d16536 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16535 p = 1 := by simpa only [d16536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19161 p hg
    simpa only [d16536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19163 (p : Pattern) (guard : d16537 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16536 p = 1 := by simpa only [d16537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19162 p hg
    simpa only [d16537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19164 (p : Pattern) (guard : d16538 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16533 p = 1 := by simpa only [d16538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19159 p hg
    simpa only [d16538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16537 p = 1 := by simpa only [d16538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19163 p hg
    simpa only [d16538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19165 (p : Pattern) (guard : d128311 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16538 p = 1 := by simpa only [d128311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19164 p hg
    simpa only [d128311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d128311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19166 (p : Pattern) (guard : d16576 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16576, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d16576, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16575 p = 1 := by simpa only [d16576, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19110 p hg
    simpa only [d16576, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19167 (p : Pattern) (guard : d16577 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16576 p = 1 := by simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19166 p hg
    simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19168 (p : Pattern) (guard : d16578 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16450 p = 1 := by simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19005 p hg
    simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16577 p = 1 := by simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19167 p hg
    simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19169 (p : Pattern) (guard : d16579 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16578 p = 1 := by simpa only [d16579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19168 p hg
    simpa only [d16579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d16579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19170 (p : Pattern) (guard : d16580 p = 1) : d48329 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16579 p = 1 := by simpa only [d16580, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19169 p hg
    simpa only [d16580, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16580, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16580, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19171 (p : Pattern) (guard : d16581 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16581, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17906 p hg
    simpa only [d16581, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16580 p = 1 := by simpa only [d16581, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19170 p hg
    simpa only [d16581, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19172 (p : Pattern) (guard : d16582 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16581 p = 1 := by simpa only [d16582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19171 p hg
    simpa only [d16582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19173 (p : Pattern) (guard : d16583 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16582 p = 1 := by simpa only [d16583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19172 p hg
    simpa only [d16583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19174 (p : Pattern) (guard : d16584 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16583 p = 1 := by simpa only [d16584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19173 p hg
    simpa only [d16584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19175 (p : Pattern) (guard : d16585 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16584 p = 1 := by simpa only [d16585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19174 p hg
    simpa only [d16585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19176 (p : Pattern) (guard : d16586 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16585 p = 1 := by simpa only [d16586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19175 p hg
    simpa only [d16586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19177 (p : Pattern) (guard : d16587 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16586 p = 1 := by simpa only [d16587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19176 p hg
    simpa only [d16587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19178 (p : Pattern) (guard : d128312 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128311 p = 1 := by simpa only [d128312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19165 p hg
    simpa only [d128312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16587 p = 1 := by simpa only [d128312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19177 p hg
    simpa only [d128312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19179 (p : Pattern) (guard : d128313 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d16506 p = 1 := by simpa only [d128313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19143 p hg
    simpa only [d128313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128312 p = 1 := by simpa only [d128313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19178 p hg
    simpa only [d128313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19180 (p : Pattern) (guard : d128314 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d16497 p = 1 := by simpa only [d128314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19134 p hg
    simpa only [d128314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128313 p = 1 := by simpa only [d128314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19179 p hg
    simpa only [d128314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19181 (p : Pattern) (guard : d16592 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16490 p = 1 := by simpa only [d16592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19040 p hg
    simpa only [d16592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19182 (p : Pattern) (guard : d16593 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16492 p = 1 := by simpa only [d16593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19042 p hg
    simpa only [d16593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19183 (p : Pattern) (guard : d16594 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16592 p = 1 := by simpa only [d16594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19181 p hg
    simpa only [d16594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16593 p = 1 := by simpa only [d16594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19182 p hg
    simpa only [d16594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19184 (p : Pattern) (guard : d16595 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16594 p = 1 := by simpa only [d16595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19183 p hg
    simpa only [d16595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19185 (p : Pattern) (guard : d16596 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16595 p = 1 := by simpa only [d16596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19184 p hg
    simpa only [d16596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19186 (p : Pattern) (guard : d16597 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16596 p = 1 := by simpa only [d16597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19185 p hg
    simpa only [d16597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19187 (p : Pattern) (guard : d16598 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16499 p = 1 := by simpa only [d16598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19049 p hg
    simpa only [d16598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19188 (p : Pattern) (guard : d16599 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16502 p = 1 := by simpa only [d16599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19052 p hg
    simpa only [d16599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19189 (p : Pattern) (guard : d16600 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16598 p = 1 := by simpa only [d16600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19187 p hg
    simpa only [d16600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16599 p = 1 := by simpa only [d16600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19188 p hg
    simpa only [d16600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19190 (p : Pattern) (guard : d16601 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16600 p = 1 := by simpa only [d16601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19189 p hg
    simpa only [d16601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19191 (p : Pattern) (guard : d16602 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16601 p = 1 := by simpa only [d16602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19190 p hg
    simpa only [d16602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19192 (p : Pattern) (guard : d16603 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16532 p = 1 := by simpa only [d16603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19100 p hg
    simpa only [d16603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19193 (p : Pattern) (guard : d16604 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16536 p = 1 := by simpa only [d16604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19104 p hg
    simpa only [d16604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19194 (p : Pattern) (guard : d16605 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16603 p = 1 := by simpa only [d16605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19192 p hg
    simpa only [d16605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16604 p = 1 := by simpa only [d16605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19193 p hg
    simpa only [d16605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19195 (p : Pattern) (guard : d128316 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16605 p = 1 := by simpa only [d128316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19194 p hg
    simpa only [d128316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d128316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19196 (p : Pattern) (guard : d16610 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16584 p = 1 := by simpa only [d16610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19119 p hg
    simpa only [d16610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19197 (p : Pattern) (guard : d16611 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16610 p = 1 := by simpa only [d16611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19196 p hg
    simpa only [d16611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19198 (p : Pattern) (guard : d16612 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16611 p = 1 := by simpa only [d16612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19197 p hg
    simpa only [d16612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19199 (p : Pattern) (guard : d128317 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128316 p = 1 := by simpa only [d128317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19195 p hg
    simpa only [d128317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16612 p = 1 := by simpa only [d128317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19198 p hg
    simpa only [d128317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19200 (p : Pattern) (guard : d128318 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d16602 p = 1 := by simpa only [d128318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19191 p hg
    simpa only [d128318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128317 p = 1 := by simpa only [d128318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19199 p hg
    simpa only [d128318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19201 (p : Pattern) (guard : d128319 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d16597 p = 1 := by simpa only [d128319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19186 p hg
    simpa only [d128319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128318 p = 1 := by simpa only [d128319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19200 p hg
    simpa only [d128319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19202 (p : Pattern) (guard : d128320 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d128314 p = 1 := by simpa only [d128320, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19180 p hg
    simpa only [d128320, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128319 p = 1 := by simpa only [d128320, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19201 p hg
    simpa only [d128320, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19203 (p : Pattern) (guard : d128321 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d128315 p = 1 := by simpa only [d128321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19126 p hg
    simpa only [d128321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128320 p = 1 := by simpa only [d128321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19202 p hg
    simpa only [d128321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19204 (p : Pattern) (guard : d16618 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16537 p = 1 := by simpa only [d16618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19163 p hg
    simpa only [d16618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16470 p = 1 := by simpa only [d16618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19023 p hg
    simpa only [d16618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19205 (p : Pattern) (guard : d16619 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16618 p = 1 := by simpa only [d16619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19204 p hg
    simpa only [d16619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19206 (p : Pattern) (guard : d16620 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16619 p = 1 := by simpa only [d16620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19205 p hg
    simpa only [d16620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19207 (p : Pattern) (guard : d16621 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16620 p = 1 := by simpa only [d16621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19206 p hg
    simpa only [d16621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19208 (p : Pattern) (guard : d16622 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16621 p = 1 := by simpa only [d16622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19207 p hg
    simpa only [d16622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19209 (p : Pattern) (guard : d16623 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16470 p = 1 := by simpa only [d16623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18994 p hg
    simpa only [d16623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19210 (p : Pattern) (guard : d16624 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16623 p = 1 := by simpa only [d16624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19209 p hg
    simpa only [d16624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19211 (p : Pattern) (guard : d16625 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16624 p = 1 := by simpa only [d16625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19210 p hg
    simpa only [d16625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19212 (p : Pattern) (guard : d16626 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16625 p = 1 := by simpa only [d16626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19211 p hg
    simpa only [d16626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19213 (p : Pattern) (guard : d16627 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16626 p = 1 := by simpa only [d16627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19212 p hg
    simpa only [d16627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19214 (p : Pattern) (guard : d16628 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16622 p = 1 := by simpa only [d16628, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19208 p hg
    simpa only [d16628, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16627 p = 1 := by simpa only [d16628, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19213 p hg
    simpa only [d16628, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19215 (p : Pattern) (guard : d16623 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16470 p = 1 := by simpa only [d16623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19023 p hg
    simpa only [d16623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19216 (p : Pattern) (guard : d16624 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16623 p = 1 := by simpa only [d16624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19215 p hg
    simpa only [d16624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19217 (p : Pattern) (guard : d16625 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16624 p = 1 := by simpa only [d16625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19216 p hg
    simpa only [d16625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19218 (p : Pattern) (guard : d16626 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16625 p = 1 := by simpa only [d16626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19217 p hg
    simpa only [d16626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19219 (p : Pattern) (guard : d16627 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16626 p = 1 := by simpa only [d16627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19218 p hg
    simpa only [d16627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19220 (p : Pattern) (guard : d16629 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16480 p = 1 := by simpa only [d16629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19030 p hg
    simpa only [d16629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19221 (p : Pattern) (guard : d16630 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16629 p = 1 := by simpa only [d16630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19220 p hg
    simpa only [d16630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19222 (p : Pattern) (guard : d16631 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16630 p = 1 := by simpa only [d16631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19221 p hg
    simpa only [d16631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19223 (p : Pattern) (guard : d16632 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16631 p = 1 := by simpa only [d16632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19222 p hg
    simpa only [d16632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19224 (p : Pattern) (guard : d16633 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16632 p = 1 := by simpa only [d16633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19223 p hg
    simpa only [d16633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19225 (p : Pattern) (guard : d16634 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16627 p = 1 := by simpa only [d16634, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19219 p hg
    simpa only [d16634, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16633 p = 1 := by simpa only [d16634, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19224 p hg
    simpa only [d16634, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19226 (p : Pattern) (guard : d16635 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d16628 p = 1 := by simpa only [d16635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19214 p hg
    simpa only [d16635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16634 p = 1 := by simpa only [d16635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19225 p hg
    simpa only [d16635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19227 (p : Pattern) (guard : d128322 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128321 p = 1 := by simpa only [d128322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19203 p hg
    simpa only [d128322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16635 p = 1 := by simpa only [d128322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19226 p hg
    simpa only [d128322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19228 (p : Pattern) (guard : d128323 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128322 p = 1 := by simpa only [d128323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19227 p hg
    simpa only [d128323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d128323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19229 (p : Pattern) (guard : d128324 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 50 with
  | false =>
    have hg : d16489 p = 1 := by simpa only [d128324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19039 p hg
    simpa only [d128324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128323 p = 1 := by simpa only [d128324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19228 p hg
    simpa only [d128324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19230 (p : Pattern) (guard : d1209 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare19231 (p : Pattern) (guard : d1210 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1209 p = 1 := by simpa only [d1210, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19230 p hg
    simpa only [d1210, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1210, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d1210, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19232 (p : Pattern) (guard : d1211 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1210 p = 1 := by simpa only [d1211, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19231 p hg
    simpa only [d1211, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1211, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d1211, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19233 (p : Pattern) (guard : d1212 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1212, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d1212, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1211 p = 1 := by simpa only [d1212, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19232 p hg
    simpa only [d1212, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19234 (p : Pattern) (guard : d1213 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1212 p = 1 := by simpa only [d1213, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19233 p hg
    simpa only [d1213, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1213, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d1213, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19235 (p : Pattern) (guard : d9752 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare19236 (p : Pattern) (guard : d9753 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9752 p = 1 := by simpa only [d9753, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19235 p hg
    simpa only [d9753, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9753, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d9753, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19237 (p : Pattern) (guard : d9755 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9753 p = 1 := by simpa only [d9755, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19236 p hg
    simpa only [d9755, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9755, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d9755, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19238 (p : Pattern) (guard : d16507 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16507, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d16507, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9755 p = 1 := by simpa only [d16507, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19237 p hg
    simpa only [d16507, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19239 (p : Pattern) (guard : d16508 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16507 p = 1 := by simpa only [d16508, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19238 p hg
    simpa only [d16508, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16508, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d16508, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19240 (p : Pattern) (guard : d16509 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1213 p = 1 := by simpa only [d16509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19234 p hg
    simpa only [d16509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16508 p = 1 := by simpa only [d16509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19239 p hg
    simpa only [d16509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19241 (p : Pattern) (guard : d9762 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare19242 (p : Pattern) (guard : d9763 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9762 p = 1 := by simpa only [d9763, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19241 p hg
    simpa only [d9763, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9763, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d9763, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19243 (p : Pattern) (guard : d9765 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9763 p = 1 := by simpa only [d9765, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19242 p hg
    simpa only [d9765, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9765, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d9765, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19244 (p : Pattern) (guard : d14836 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14836, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d14836, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9765 p = 1 := by simpa only [d14836, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19243 p hg
    simpa only [d14836, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19245 (p : Pattern) (guard : d14837 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14836 p = 1 := by simpa only [d14837, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19244 p hg
    simpa only [d14837, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14837, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d14837, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19246 (p : Pattern) (guard : d9777 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare19247 (p : Pattern) (guard : d9778 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9777 p = 1 := by simpa only [d9778, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19246 p hg
    simpa only [d9778, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9778, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d9778, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19248 (p : Pattern) (guard : d9780 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9778 p = 1 := by simpa only [d9780, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19247 p hg
    simpa only [d9780, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9780, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d9780, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19249 (p : Pattern) (guard : d14758 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14758, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d14758, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9780 p = 1 := by simpa only [d14758, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19248 p hg
    simpa only [d14758, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
