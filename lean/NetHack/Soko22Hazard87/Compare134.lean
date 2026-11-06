import NetHack.Soko22Hazard87.Compare133
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare33500 (p : Pattern) (guard : d295292 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295291 p = 1 := by simpa only [d295292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33499 p hg
    simpa only [d295292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33501 (p : Pattern) (guard : d295293 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295290 p = 1 := by simpa only [d295293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33498 p hg
    simpa only [d295293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295292 p = 1 := by simpa only [d295293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33500 p hg
    simpa only [d295293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33502 (p : Pattern) (guard : d295294 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295293 p = 1 := by simpa only [d295294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33501 p hg
    simpa only [d295294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33503 (p : Pattern) (guard : d295295 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295294 p = 1 := by simpa only [d295295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33502 p hg
    simpa only [d295295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33504 (p : Pattern) (guard : d295296 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295295 p = 1 := by simpa only [d295296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33503 p hg
    simpa only [d295296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33505 (p : Pattern) (guard : d295297 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295262 p = 1 := by simpa only [d295297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33423 p hg
    simpa only [d295297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33506 (p : Pattern) (guard : d295298 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295297 p = 1 := by simpa only [d295298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33505 p hg
    simpa only [d295298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33507 (p : Pattern) (guard : d295299 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295298 p = 1 := by simpa only [d295299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33506 p hg
    simpa only [d295299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33508 (p : Pattern) (guard : d295300 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295266 p = 1 := by simpa only [d295300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33427 p hg
    simpa only [d295300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33509 (p : Pattern) (guard : d295301 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295300 p = 1 := by simpa only [d295301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33508 p hg
    simpa only [d295301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33510 (p : Pattern) (guard : d295302 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295301 p = 1 := by simpa only [d295302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33509 p hg
    simpa only [d295302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33511 (p : Pattern) (guard : d295303 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295299 p = 1 := by simpa only [d295303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33507 p hg
    simpa only [d295303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295302 p = 1 := by simpa only [d295303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33510 p hg
    simpa only [d295303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33512 (p : Pattern) (guard : d295304 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295303 p = 1 := by simpa only [d295304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33511 p hg
    simpa only [d295304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33513 (p : Pattern) (guard : d295305 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295304 p = 1 := by simpa only [d295305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33512 p hg
    simpa only [d295305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33514 (p : Pattern) (guard : d295308 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295308, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32016 p hg
    simpa only [d295308, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295307 p = 1 := by simpa only [d295308, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33465 p hg
    simpa only [d295308, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33515 (p : Pattern) (guard : d295309 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295308 p = 1 := by simpa only [d295309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33514 p hg
    simpa only [d295309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295247 p = 1 := by simpa only [d295309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33411 p hg
    simpa only [d295309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33516 (p : Pattern) (guard : d295310 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295309 p = 1 := by simpa only [d295310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33515 p hg
    simpa only [d295310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295252 p = 1 := by simpa only [d295310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33413 p hg
    simpa only [d295310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33517 (p : Pattern) (guard : d295311 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295310 p = 1 := by simpa only [d295311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33516 p hg
    simpa only [d295311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d295311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33518 (p : Pattern) (guard : d295312 p = 1) : d49894 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295311 p = 1 := by simpa only [d295312, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33517 p hg
    simpa only [d295312, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295312, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d295312, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33519 (p : Pattern) (guard : d295313 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295313, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32015 p hg
    simpa only [d295313, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295312 p = 1 := by simpa only [d295313, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33518 p hg
    simpa only [d295313, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33520 (p : Pattern) (guard : d295314 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295313 p = 1 := by simpa only [d295314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33519 p hg
    simpa only [d295314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295257 p = 1 := by simpa only [d295314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33418 p hg
    simpa only [d295314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33521 (p : Pattern) (guard : d295315 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295314 p = 1 := by simpa only [d295315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33520 p hg
    simpa only [d295315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33522 (p : Pattern) (guard : d295316 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295315 p = 1 := by simpa only [d295316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33521 p hg
    simpa only [d295316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33523 (p : Pattern) (guard : d295317 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295316 p = 1 := by simpa only [d295317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33522 p hg
    simpa only [d295317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33524 (p : Pattern) (guard : d295318 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295317 p = 1 := by simpa only [d295318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33523 p hg
    simpa only [d295318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295265 p = 1 := by simpa only [d295318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33426 p hg
    simpa only [d295318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33525 (p : Pattern) (guard : d295319 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d295318 p = 1 := by simpa only [d295319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33524 p hg
    simpa only [d295319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33526 (p : Pattern) (guard : d295323 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295323, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32016 p hg
    simpa only [d295323, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295322 p = 1 := by simpa only [d295323, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33480 p hg
    simpa only [d295323, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33527 (p : Pattern) (guard : d295324 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295323 p = 1 := by simpa only [d295324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33526 p hg
    simpa only [d295324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d295324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33528 (p : Pattern) (guard : d295325 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295252 p = 1 := by simpa only [d295325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33413 p hg
    simpa only [d295325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295324 p = 1 := by simpa only [d295325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33527 p hg
    simpa only [d295325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33529 (p : Pattern) (guard : d295326 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295325 p = 1 := by simpa only [d295326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33528 p hg
    simpa only [d295326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d295326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33530 (p : Pattern) (guard : d295327 p = 1) : d49894 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295326 p = 1 := by simpa only [d295327, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33529 p hg
    simpa only [d295327, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295327, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d295327, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33531 (p : Pattern) (guard : d295328 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295328, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32015 p hg
    simpa only [d295328, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295327 p = 1 := by simpa only [d295328, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33530 p hg
    simpa only [d295328, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33532 (p : Pattern) (guard : d295329 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295328 p = 1 := by simpa only [d295329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33531 p hg
    simpa only [d295329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33533 (p : Pattern) (guard : d295330 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295329 p = 1 := by simpa only [d295330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33532 p hg
    simpa only [d295330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33534 (p : Pattern) (guard : d295331 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295330 p = 1 := by simpa only [d295331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33533 p hg
    simpa only [d295331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33535 (p : Pattern) (guard : d295332 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295331 p = 1 := by simpa only [d295332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33534 p hg
    simpa only [d295332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33536 (p : Pattern) (guard : d295333 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295332 p = 1 := by simpa only [d295333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33535 p hg
    simpa only [d295333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33537 (p : Pattern) (guard : d295334 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d295333 p = 1 := by simpa only [d295334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33536 p hg
    simpa only [d295334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33538 (p : Pattern) (guard : d295335 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295319 p = 1 := by simpa only [d295335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33525 p hg
    simpa only [d295335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295334 p = 1 := by simpa only [d295335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33537 p hg
    simpa only [d295335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33539 (p : Pattern) (guard : d295336 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d295305 p = 1 := by simpa only [d295336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33513 p hg
    simpa only [d295336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295335 p = 1 := by simpa only [d295336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33538 p hg
    simpa only [d295336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33540 (p : Pattern) (guard : d295337 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d295296 p = 1 := by simpa only [d295337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33504 p hg
    simpa only [d295337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295336 p = 1 := by simpa only [d295337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33539 p hg
    simpa only [d295337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33541 (p : Pattern) (guard : d295339 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295289 p = 1 := by simpa only [d295339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33447 p hg
    simpa only [d295339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33542 (p : Pattern) (guard : d295340 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295291 p = 1 := by simpa only [d295340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33449 p hg
    simpa only [d295340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33543 (p : Pattern) (guard : d295341 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295339 p = 1 := by simpa only [d295341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33541 p hg
    simpa only [d295341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295340 p = 1 := by simpa only [d295341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33542 p hg
    simpa only [d295341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33544 (p : Pattern) (guard : d295342 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295341 p = 1 := by simpa only [d295342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33543 p hg
    simpa only [d295342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33545 (p : Pattern) (guard : d295343 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295342 p = 1 := by simpa only [d295343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33544 p hg
    simpa only [d295343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33546 (p : Pattern) (guard : d295344 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295343 p = 1 := by simpa only [d295344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33545 p hg
    simpa only [d295344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33547 (p : Pattern) (guard : d295345 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295298 p = 1 := by simpa only [d295345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33456 p hg
    simpa only [d295345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33548 (p : Pattern) (guard : d295346 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295301 p = 1 := by simpa only [d295346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33459 p hg
    simpa only [d295346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33549 (p : Pattern) (guard : d295347 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295345 p = 1 := by simpa only [d295347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33547 p hg
    simpa only [d295347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295346 p = 1 := by simpa only [d295347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33548 p hg
    simpa only [d295347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33550 (p : Pattern) (guard : d295348 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295347 p = 1 := by simpa only [d295348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33549 p hg
    simpa only [d295348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33551 (p : Pattern) (guard : d295349 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295348 p = 1 := by simpa only [d295349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33550 p hg
    simpa only [d295349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33552 (p : Pattern) (guard : d295350 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295316 p = 1 := by simpa only [d295350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33474 p hg
    simpa only [d295350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33553 (p : Pattern) (guard : d295351 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295350 p = 1 := by simpa only [d295351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33552 p hg
    simpa only [d295351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295278 p = 1 := by simpa only [d295351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33436 p hg
    simpa only [d295351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33554 (p : Pattern) (guard : d295352 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d295351 p = 1 := by simpa only [d295352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33553 p hg
    simpa only [d295352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33555 (p : Pattern) (guard : d295353 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295331 p = 1 := by simpa only [d295353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33489 p hg
    simpa only [d295353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33556 (p : Pattern) (guard : d295354 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295353 p = 1 := by simpa only [d295354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33555 p hg
    simpa only [d295354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33557 (p : Pattern) (guard : d295355 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d295354 p = 1 := by simpa only [d295355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33556 p hg
    simpa only [d295355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33558 (p : Pattern) (guard : d295356 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295352 p = 1 := by simpa only [d295356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33554 p hg
    simpa only [d295356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295355 p = 1 := by simpa only [d295356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33557 p hg
    simpa only [d295356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33559 (p : Pattern) (guard : d295357 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d295349 p = 1 := by simpa only [d295357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33551 p hg
    simpa only [d295357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295356 p = 1 := by simpa only [d295357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33558 p hg
    simpa only [d295357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33560 (p : Pattern) (guard : d295358 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d295344 p = 1 := by simpa only [d295358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33546 p hg
    simpa only [d295358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295357 p = 1 := by simpa only [d295358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33559 p hg
    simpa only [d295358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33561 (p : Pattern) (guard : d295359 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d295337 p = 1 := by simpa only [d295359, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33540 p hg
    simpa only [d295359, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295358 p = 1 := by simpa only [d295359, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33560 p hg
    simpa only [d295359, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33562 (p : Pattern) (guard : d295360 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d295338 p = 1 := by simpa only [d295360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33496 p hg
    simpa only [d295360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295359 p = 1 := by simpa only [d295360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33561 p hg
    simpa only [d295360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33563 (p : Pattern) (guard : d295361 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295269 p = 1 := by simpa only [d295361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33402 p hg
    simpa only [d295361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33564 (p : Pattern) (guard : d295362 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295361 p = 1 := by simpa only [d295362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33563 p hg
    simpa only [d295362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33565 (p : Pattern) (guard : d295363 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295362 p = 1 := by simpa only [d295363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33564 p hg
    simpa only [d295363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33566 (p : Pattern) (guard : d295364 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295363 p = 1 := by simpa only [d295364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33565 p hg
    simpa only [d295364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33567 (p : Pattern) (guard : d295365 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295364 p = 1 := by simpa only [d295365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33566 p hg
    simpa only [d295365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33568 (p : Pattern) (guard : d295366 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d295274 p = 1 := by simpa only [d295366, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33435 p hg
    simpa only [d295366, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295365 p = 1 := by simpa only [d295366, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33567 p hg
    simpa only [d295366, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33569 (p : Pattern) (guard : d295361 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295269 p = 1 := by simpa only [d295361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33430 p hg
    simpa only [d295361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33570 (p : Pattern) (guard : d295362 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295361 p = 1 := by simpa only [d295362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33569 p hg
    simpa only [d295362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33571 (p : Pattern) (guard : d295363 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295362 p = 1 := by simpa only [d295363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33570 p hg
    simpa only [d295363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33572 (p : Pattern) (guard : d295364 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295363 p = 1 := by simpa only [d295364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33571 p hg
    simpa only [d295364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33573 (p : Pattern) (guard : d295365 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295364 p = 1 := by simpa only [d295365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33572 p hg
    simpa only [d295365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33574 (p : Pattern) (guard : d295367 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295279 p = 1 := by simpa only [d295367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33437 p hg
    simpa only [d295367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33575 (p : Pattern) (guard : d295368 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295367 p = 1 := by simpa only [d295368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33574 p hg
    simpa only [d295368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33576 (p : Pattern) (guard : d295369 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295368 p = 1 := by simpa only [d295369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33575 p hg
    simpa only [d295369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33577 (p : Pattern) (guard : d295370 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295369 p = 1 := by simpa only [d295370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33576 p hg
    simpa only [d295370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33578 (p : Pattern) (guard : d295371 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d295371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295370 p = 1 := by simpa only [d295371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33577 p hg
    simpa only [d295371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33579 (p : Pattern) (guard : d295372 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d295365 p = 1 := by simpa only [d295372, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33573 p hg
    simpa only [d295372, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295371 p = 1 := by simpa only [d295372, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33578 p hg
    simpa only [d295372, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33580 (p : Pattern) (guard : d295373 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d295366 p = 1 := by simpa only [d295373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33568 p hg
    simpa only [d295373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295372 p = 1 := by simpa only [d295373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33579 p hg
    simpa only [d295373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33581 (p : Pattern) (guard : d295374 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d295360 p = 1 := by simpa only [d295374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33562 p hg
    simpa only [d295374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295373 p = 1 := by simpa only [d295374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33580 p hg
    simpa only [d295374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33582 (p : Pattern) (guard : d295375 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d295374 p = 1 := by simpa only [d295375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33581 p hg
    simpa only [d295375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31966 p hg
    simpa only [d295375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33583 (p : Pattern) (guard : d295376 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d295288 p = 1 := by simpa only [d295376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33446 p hg
    simpa only [d295376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295375 p = 1 := by simpa only [d295376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33582 p hg
    simpa only [d295376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33584 (p : Pattern) (guard : d2014 p = 1) : d47706 p ≤ (1 : Int) + d47706 p := by
  omega
theorem compare33585 (p : Pattern) (guard : d32701 p = 1) : d49927 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2014 p = 1 := by simpa only [d32701, d49927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33584 p hg
    simpa only [d32701, d49927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32701, d49927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32053 p hg
    simpa only [d32701, d49927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33586 (p : Pattern) (guard : d32702 p = 1) : d49927 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d32701 p = 1 := by simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33585 p hg
    simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32051 p hg
    simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33587 (p : Pattern) (guard : d32703 p = 1) : d49927 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d32702 p = 1 := by simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33586 p hg
    simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32051 p hg
    simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33588 (p : Pattern) (guard : d294185 p = 1) : d49927 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32051 p hg
    simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32703 p = 1 := by simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33587 p hg
    simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33589 (p : Pattern) (guard : d294186 p = 1) : d49927 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d294185 p = 1 := by simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33588 p hg
    simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32051 p hg
    simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33590 (p : Pattern) (guard : d294187 p = 1) : d49929 p ≤ (1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294186 p = 1 := by simpa only [d294187, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33589 p hg
    simpa only [d294187, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294187, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32059 p hg
    simpa only [d294187, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33591 (p : Pattern) (guard : d294188 p = 1) : d49929 p ≤ (1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294187 p = 1 := by simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33590 p hg
    simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32061 p hg
    simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33592 (p : Pattern) (guard : d294189 p = 1) : d49957 p ≤ (1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294188 p = 1 := by simpa only [d294189, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33591 p hg
    simpa only [d294189, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294189, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32063 p hg
    simpa only [d294189, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33593 (p : Pattern) (guard : d294190 p = 1) : d49958 p ≤ (1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294189 p = 1 := by simpa only [d294190, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33592 p hg
    simpa only [d294190, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294190, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d294190, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33594 (p : Pattern) (guard : d294191 p = 1) : d49978 p ≤ (1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294191, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32050 p hg
    simpa only [d294191, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294190 p = 1 := by simpa only [d294191, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33593 p hg
    simpa only [d294191, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33595 (p : Pattern) (guard : d294192 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294191 p = 1 := by simpa only [d294192, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33594 p hg
    simpa only [d294192, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294192, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32068 p hg
    simpa only [d294192, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33596 (p : Pattern) (guard : d295242 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32049 p hg
    simpa only [d295242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294192 p = 1 := by simpa only [d295242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33595 p hg
    simpa only [d295242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33597 (p : Pattern) (guard : d295243 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32049 p hg
    simpa only [d295243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295242 p = 1 := by simpa only [d295243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33596 p hg
    simpa only [d295243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33598 (p : Pattern) (guard : d295306 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32049 p hg
    simpa only [d295306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295243 p = 1 := by simpa only [d295306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33597 p hg
    simpa only [d295306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33599 (p : Pattern) (guard : d295307 p = 1) : d49983 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295307, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32048 p hg
    simpa only [d295307, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295306 p = 1 := by simpa only [d295307, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33598 p hg
    simpa only [d295307, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33600 (p : Pattern) (guard : d295308 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295308, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32047 p hg
    simpa only [d295308, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295307 p = 1 := by simpa only [d295308, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33599 p hg
    simpa only [d295308, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33601 (p : Pattern) (guard : d294204 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d294192 p = 1 := by simpa only [d294204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33595 p hg
    simpa only [d294204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32049 p hg
    simpa only [d294204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33602 (p : Pattern) (guard : d295244 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d295242 p = 1 := by simpa only [d295244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33596 p hg
    simpa only [d295244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294204 p = 1 := by simpa only [d295244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33601 p hg
    simpa only [d295244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33603 (p : Pattern) (guard : d295245 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295243 p = 1 := by simpa only [d295245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33597 p hg
    simpa only [d295245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295244 p = 1 := by simpa only [d295245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33602 p hg
    simpa only [d295245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33604 (p : Pattern) (guard : d295246 p = 1) : d49983 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295246, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32048 p hg
    simpa only [d295246, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295245 p = 1 := by simpa only [d295246, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33603 p hg
    simpa only [d295246, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33605 (p : Pattern) (guard : d295247 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295247, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32047 p hg
    simpa only [d295247, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295246 p = 1 := by simpa only [d295247, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33604 p hg
    simpa only [d295247, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33606 (p : Pattern) (guard : d295309 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295308 p = 1 := by simpa only [d295309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33600 p hg
    simpa only [d295309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295247 p = 1 := by simpa only [d295309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33605 p hg
    simpa only [d295309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33607 (p : Pattern) (guard : d295248 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294204 p = 1 := by simpa only [d295248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33601 p hg
    simpa only [d295248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32049 p hg
    simpa only [d295248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33608 (p : Pattern) (guard : d295249 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295244 p = 1 := by simpa only [d295249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33602 p hg
    simpa only [d295249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295248 p = 1 := by simpa only [d295249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33607 p hg
    simpa only [d295249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33609 (p : Pattern) (guard : d295250 p = 1) : d49983 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295250, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32048 p hg
    simpa only [d295250, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295249 p = 1 := by simpa only [d295250, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33608 p hg
    simpa only [d295250, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33610 (p : Pattern) (guard : d295251 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295251, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32047 p hg
    simpa only [d295251, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295250 p = 1 := by simpa only [d295251, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33609 p hg
    simpa only [d295251, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33611 (p : Pattern) (guard : d295252 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295247 p = 1 := by simpa only [d295252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33605 p hg
    simpa only [d295252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295251 p = 1 := by simpa only [d295252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33610 p hg
    simpa only [d295252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33612 (p : Pattern) (guard : d295310 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295309 p = 1 := by simpa only [d295310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33606 p hg
    simpa only [d295310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295252 p = 1 := by simpa only [d295310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33611 p hg
    simpa only [d295310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33613 (p : Pattern) (guard : d295311 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295310 p = 1 := by simpa only [d295311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33612 p hg
    simpa only [d295311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d295311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33614 (p : Pattern) (guard : d295312 p = 1) : d49999 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295311 p = 1 := by simpa only [d295312, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33613 p hg
    simpa only [d295312, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295312, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32079 p hg
    simpa only [d295312, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33615 (p : Pattern) (guard : d295313 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295313, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32046 p hg
    simpa only [d295313, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295312 p = 1 := by simpa only [d295313, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33614 p hg
    simpa only [d295313, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33616 (p : Pattern) (guard : d295253 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295251 p = 1 := by simpa only [d295253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33610 p hg
    simpa only [d295253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d295253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33617 (p : Pattern) (guard : d295254 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295252 p = 1 := by simpa only [d295254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33611 p hg
    simpa only [d295254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295253 p = 1 := by simpa only [d295254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33616 p hg
    simpa only [d295254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33618 (p : Pattern) (guard : d295255 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295254 p = 1 := by simpa only [d295255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33617 p hg
    simpa only [d295255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d295255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33619 (p : Pattern) (guard : d295256 p = 1) : d49999 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295255 p = 1 := by simpa only [d295256, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33618 p hg
    simpa only [d295256, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295256, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32079 p hg
    simpa only [d295256, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33620 (p : Pattern) (guard : d295257 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295257, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32046 p hg
    simpa only [d295257, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295256 p = 1 := by simpa only [d295257, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33619 p hg
    simpa only [d295257, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33621 (p : Pattern) (guard : d295314 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295313 p = 1 := by simpa only [d295314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33615 p hg
    simpa only [d295314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295257 p = 1 := by simpa only [d295314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33620 p hg
    simpa only [d295314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33622 (p : Pattern) (guard : d295315 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295314 p = 1 := by simpa only [d295315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33621 p hg
    simpa only [d295315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33623 (p : Pattern) (guard : d295316 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295315 p = 1 := by simpa only [d295316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33622 p hg
    simpa only [d295316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33624 (p : Pattern) (guard : d295350 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295316 p = 1 := by simpa only [d295350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33623 p hg
    simpa only [d295350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33625 (p : Pattern) (guard : d295258 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295253 p = 1 := by simpa only [d295258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33616 p hg
    simpa only [d295258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d295258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33626 (p : Pattern) (guard : d295259 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295258 p = 1 := by simpa only [d295259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33625 p hg
    simpa only [d295259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d295259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33627 (p : Pattern) (guard : d295260 p = 1) : d49999 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295259 p = 1 := by simpa only [d295260, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33626 p hg
    simpa only [d295260, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295260, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32079 p hg
    simpa only [d295260, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33628 (p : Pattern) (guard : d295261 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295261, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32046 p hg
    simpa only [d295261, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295260 p = 1 := by simpa only [d295261, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33627 p hg
    simpa only [d295261, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33629 (p : Pattern) (guard : d295262 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295257 p = 1 := by simpa only [d295262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33620 p hg
    simpa only [d295262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295261 p = 1 := by simpa only [d295262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33628 p hg
    simpa only [d295262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33630 (p : Pattern) (guard : d295263 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295262 p = 1 := by simpa only [d295263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33629 p hg
    simpa only [d295263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33631 (p : Pattern) (guard : d295264 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295263 p = 1 := by simpa only [d295264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33630 p hg
    simpa only [d295264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33632 (p : Pattern) (guard : d295278 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295264 p = 1 := by simpa only [d295278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33631 p hg
    simpa only [d295278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33633 (p : Pattern) (guard : d295351 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295350 p = 1 := by simpa only [d295351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33624 p hg
    simpa only [d295351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295278 p = 1 := by simpa only [d295351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33632 p hg
    simpa only [d295351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33634 (p : Pattern) (guard : d295352 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d295351 p = 1 := by simpa only [d295352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33633 p hg
    simpa only [d295352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33635 (p : Pattern) (guard : d295320 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d295242 p = 1 := by simpa only [d295320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33596 p hg
    simpa only [d295320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32049 p hg
    simpa only [d295320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33636 (p : Pattern) (guard : d295321 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295320 p = 1 := by simpa only [d295321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33635 p hg
    simpa only [d295321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32049 p hg
    simpa only [d295321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33637 (p : Pattern) (guard : d295322 p = 1) : d49983 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295322, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32048 p hg
    simpa only [d295322, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295321 p = 1 := by simpa only [d295322, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33636 p hg
    simpa only [d295322, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33638 (p : Pattern) (guard : d295323 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295323, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32047 p hg
    simpa only [d295323, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295322 p = 1 := by simpa only [d295323, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33637 p hg
    simpa only [d295323, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33639 (p : Pattern) (guard : d295324 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295323 p = 1 := by simpa only [d295324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33638 p hg
    simpa only [d295324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d295324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33640 (p : Pattern) (guard : d295325 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295252 p = 1 := by simpa only [d295325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33611 p hg
    simpa only [d295325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295324 p = 1 := by simpa only [d295325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33639 p hg
    simpa only [d295325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33641 (p : Pattern) (guard : d295326 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295325 p = 1 := by simpa only [d295326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33640 p hg
    simpa only [d295326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d295326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33642 (p : Pattern) (guard : d295327 p = 1) : d49999 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295326 p = 1 := by simpa only [d295327, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33641 p hg
    simpa only [d295327, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295327, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32079 p hg
    simpa only [d295327, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33643 (p : Pattern) (guard : d295328 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295328, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32046 p hg
    simpa only [d295328, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295327 p = 1 := by simpa only [d295328, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33642 p hg
    simpa only [d295328, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33644 (p : Pattern) (guard : d295329 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295328 p = 1 := by simpa only [d295329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33643 p hg
    simpa only [d295329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33645 (p : Pattern) (guard : d295330 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295329 p = 1 := by simpa only [d295330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33644 p hg
    simpa only [d295330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33646 (p : Pattern) (guard : d295331 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295330 p = 1 := by simpa only [d295331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33645 p hg
    simpa only [d295331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33647 (p : Pattern) (guard : d295353 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295331 p = 1 := by simpa only [d295353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33646 p hg
    simpa only [d295353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33648 (p : Pattern) (guard : d295354 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295353 p = 1 := by simpa only [d295354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33647 p hg
    simpa only [d295354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33649 (p : Pattern) (guard : d295355 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d295354 p = 1 := by simpa only [d295355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33648 p hg
    simpa only [d295355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33650 (p : Pattern) (guard : d295356 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295352 p = 1 := by simpa only [d295356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33634 p hg
    simpa only [d295356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295355 p = 1 := by simpa only [d295356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33649 p hg
    simpa only [d295356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33651 (p : Pattern) (guard : d295377 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295356 p = 1 := by simpa only [d295377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33650 p hg
    simpa only [d295377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33652 (p : Pattern) (guard : d295378 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295377 p = 1 := by simpa only [d295378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33651 p hg
    simpa only [d295378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33653 (p : Pattern) (guard : d295379 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295379, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295379, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295378 p = 1 := by simpa only [d295379, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33652 p hg
    simpa only [d295379, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33654 (p : Pattern) (guard : d295380 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32044 p hg
    simpa only [d295380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295379 p = 1 := by simpa only [d295380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33653 p hg
    simpa only [d295380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33655 (p : Pattern) (guard : d295266 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295261 p = 1 := by simpa only [d295266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33628 p hg
    simpa only [d295266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33656 (p : Pattern) (guard : d295267 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295266 p = 1 := by simpa only [d295267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33655 p hg
    simpa only [d295267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33657 (p : Pattern) (guard : d295268 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295267 p = 1 := by simpa only [d295268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33656 p hg
    simpa only [d295268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33658 (p : Pattern) (guard : d295279 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295268 p = 1 := by simpa only [d295279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33657 p hg
    simpa only [d295279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33659 (p : Pattern) (guard : d295367 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295279 p = 1 := by simpa only [d295367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33658 p hg
    simpa only [d295367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33660 (p : Pattern) (guard : d295368 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295367 p = 1 := by simpa only [d295368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33659 p hg
    simpa only [d295368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33661 (p : Pattern) (guard : d295369 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295368 p = 1 := by simpa only [d295369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33660 p hg
    simpa only [d295369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33662 (p : Pattern) (guard : d295370 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295369 p = 1 := by simpa only [d295370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33661 p hg
    simpa only [d295370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33663 (p : Pattern) (guard : d295371 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d295371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295370 p = 1 := by simpa only [d295371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33662 p hg
    simpa only [d295371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33664 (p : Pattern) (guard : d295381 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295381, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d295381, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295371 p = 1 := by simpa only [d295381, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33663 p hg
    simpa only [d295381, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33665 (p : Pattern) (guard : d295382 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32044 p hg
    simpa only [d295382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295381 p = 1 := by simpa only [d295382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33664 p hg
    simpa only [d295382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33666 (p : Pattern) (guard : d295383 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d295380 p = 1 := by simpa only [d295383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33654 p hg
    simpa only [d295383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295382 p = 1 := by simpa only [d295383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33665 p hg
    simpa only [d295383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33667 (p : Pattern) (guard : d295384 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d295383 p = 1 := by simpa only [d295384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33666 p hg
    simpa only [d295384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32044 p hg
    simpa only [d295384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33668 (p : Pattern) (guard : d295385 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d295384 p = 1 := by simpa only [d295385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33667 p hg
    simpa only [d295385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32044 p hg
    simpa only [d295385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33669 (p : Pattern) (guard : d295386 p = 1) : d50002 p ≤ (1 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d295376 p = 1 := by simpa only [d295386, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33583 p hg
    simpa only [d295386, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295385 p = 1 := by simpa only [d295386, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33668 p hg
    simpa only [d295386, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33670 (p : Pattern) (guard : d2014 p = 1) : d47630 p ≤ (1 : Int) + d47630 p := by
  omega
theorem compare33671 (p : Pattern) (guard : d32701 p = 1) : d49808 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2014 p = 1 := by simpa only [d32701, d49808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33670 p hg
    simpa only [d32701, d49808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32701, d49808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32105 p hg
    simpa only [d32701, d49808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33672 (p : Pattern) (guard : d32702 p = 1) : d49808 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d32701 p = 1 := by simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33671 p hg
    simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32103 p hg
    simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33673 (p : Pattern) (guard : d32703 p = 1) : d49808 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d32702 p = 1 := by simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33672 p hg
    simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32103 p hg
    simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33674 (p : Pattern) (guard : d294185 p = 1) : d49808 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32103 p hg
    simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32703 p = 1 := by simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33673 p hg
    simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33675 (p : Pattern) (guard : d294186 p = 1) : d49808 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d294185 p = 1 := by simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33674 p hg
    simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32103 p hg
    simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33676 (p : Pattern) (guard : d294187 p = 1) : d49831 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294186 p = 1 := by simpa only [d294187, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33675 p hg
    simpa only [d294187, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294187, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32111 p hg
    simpa only [d294187, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33677 (p : Pattern) (guard : d294188 p = 1) : d49831 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294187 p = 1 := by simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33676 p hg
    simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32102 p hg
    simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33678 (p : Pattern) (guard : d294360 p = 1) : d49831 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32102 p hg
    simpa only [d294360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294188 p = 1 := by simpa only [d294360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33677 p hg
    simpa only [d294360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33679 (p : Pattern) (guard : d294189 p = 1) : d50030 p ≤ (1 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294188 p = 1 := by simpa only [d294189, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33369 p hg
    simpa only [d294189, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294189, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32063 p hg
    simpa only [d294189, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33680 (p : Pattern) (guard : d294361 p = 1) : d50031 p ≤ (1 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294360 p = 1 := by simpa only [d294361, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33678 p hg
    simpa only [d294361, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294189 p = 1 := by simpa only [d294361, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33679 p hg
    simpa only [d294361, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33681 (p : Pattern) (guard : d2014 p = 1) : d47634 p ≤ (1 : Int) + d47634 p := by
  omega
theorem compare33682 (p : Pattern) (guard : d32701 p = 1) : d49811 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2014 p = 1 := by simpa only [d32701, d49811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33681 p hg
    simpa only [d32701, d49811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32701, d49811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32119 p hg
    simpa only [d32701, d49811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33683 (p : Pattern) (guard : d32702 p = 1) : d49811 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d32701 p = 1 := by simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33682 p hg
    simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32117 p hg
    simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33684 (p : Pattern) (guard : d32703 p = 1) : d49811 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d32702 p = 1 := by simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33683 p hg
    simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32117 p hg
    simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33685 (p : Pattern) (guard : d294185 p = 1) : d49811 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32117 p hg
    simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32703 p = 1 := by simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33684 p hg
    simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33686 (p : Pattern) (guard : d294186 p = 1) : d49811 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d294185 p = 1 := by simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33685 p hg
    simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32117 p hg
    simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33687 (p : Pattern) (guard : d294187 p = 1) : d49857 p ≤ (1 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294186 p = 1 := by simpa only [d294187, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33686 p hg
    simpa only [d294187, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294187, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32125 p hg
    simpa only [d294187, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33688 (p : Pattern) (guard : d294188 p = 1) : d49857 p ≤ (1 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294187 p = 1 := by simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33687 p hg
    simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33689 (p : Pattern) (guard : d294189 p = 1) : d49865 p ≤ (1 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294188 p = 1 := by simpa only [d294189, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33688 p hg
    simpa only [d294189, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294189, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d294189, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33690 (p : Pattern) (guard : d294190 p = 1) : d49866 p ≤ (1 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294189 p = 1 := by simpa only [d294190, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33689 p hg
    simpa only [d294190, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294190, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d294190, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33691 (p : Pattern) (guard : d294362 p = 1) : d50032 p ≤ (1 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d294361 p = 1 := by simpa only [d294362, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33680 p hg
    simpa only [d294362, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294190 p = 1 := by simpa only [d294362, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33690 p hg
    simpa only [d294362, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33692 (p : Pattern) (guard : d294363 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294362 p = 1 := by simpa only [d294363, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33691 p hg
    simpa only [d294363, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294363, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32132 p hg
    simpa only [d294363, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33693 (p : Pattern) (guard : d295387 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32101 p hg
    simpa only [d295387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294363 p = 1 := by simpa only [d295387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33692 p hg
    simpa only [d295387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33694 (p : Pattern) (guard : d295388 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32101 p hg
    simpa only [d295388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295387 p = 1 := by simpa only [d295388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33693 p hg
    simpa only [d295388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33695 (p : Pattern) (guard : d295389 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32101 p hg
    simpa only [d295389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295388 p = 1 := by simpa only [d295389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33694 p hg
    simpa only [d295389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33696 (p : Pattern) (guard : d295390 p = 1) : d50037 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295390, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32100 p hg
    simpa only [d295390, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295389 p = 1 := by simpa only [d295390, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33695 p hg
    simpa only [d295390, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33697 (p : Pattern) (guard : d295391 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295391, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32099 p hg
    simpa only [d295391, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295390 p = 1 := by simpa only [d295391, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33696 p hg
    simpa only [d295391, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33698 (p : Pattern) (guard : d294369 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d294363 p = 1 := by simpa only [d294369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33692 p hg
    simpa only [d294369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32101 p hg
    simpa only [d294369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33699 (p : Pattern) (guard : d295392 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d295387 p = 1 := by simpa only [d295392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33693 p hg
    simpa only [d295392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294369 p = 1 := by simpa only [d295392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33698 p hg
    simpa only [d295392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33700 (p : Pattern) (guard : d295393 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295388 p = 1 := by simpa only [d295393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33694 p hg
    simpa only [d295393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295392 p = 1 := by simpa only [d295393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33699 p hg
    simpa only [d295393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33701 (p : Pattern) (guard : d295394 p = 1) : d50037 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295394, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32100 p hg
    simpa only [d295394, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295393 p = 1 := by simpa only [d295394, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33700 p hg
    simpa only [d295394, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33702 (p : Pattern) (guard : d295395 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295395, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32099 p hg
    simpa only [d295395, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295394 p = 1 := by simpa only [d295395, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33701 p hg
    simpa only [d295395, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33703 (p : Pattern) (guard : d295396 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295391 p = 1 := by simpa only [d295396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33697 p hg
    simpa only [d295396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295395 p = 1 := by simpa only [d295396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33702 p hg
    simpa only [d295396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33704 (p : Pattern) (guard : d295397 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294369 p = 1 := by simpa only [d295397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33698 p hg
    simpa only [d295397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32101 p hg
    simpa only [d295397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33705 (p : Pattern) (guard : d295398 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295392 p = 1 := by simpa only [d295398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33699 p hg
    simpa only [d295398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295397 p = 1 := by simpa only [d295398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33704 p hg
    simpa only [d295398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33706 (p : Pattern) (guard : d295399 p = 1) : d50037 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295399, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32100 p hg
    simpa only [d295399, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295398 p = 1 := by simpa only [d295399, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33705 p hg
    simpa only [d295399, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33707 (p : Pattern) (guard : d295400 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295400, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32099 p hg
    simpa only [d295400, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295399 p = 1 := by simpa only [d295400, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33706 p hg
    simpa only [d295400, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33708 (p : Pattern) (guard : d295401 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295395 p = 1 := by simpa only [d295401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33702 p hg
    simpa only [d295401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295400 p = 1 := by simpa only [d295401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33707 p hg
    simpa only [d295401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33709 (p : Pattern) (guard : d295402 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295396 p = 1 := by simpa only [d295402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33703 p hg
    simpa only [d295402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295401 p = 1 := by simpa only [d295402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33708 p hg
    simpa only [d295402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33710 (p : Pattern) (guard : d295403 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295402 p = 1 := by simpa only [d295403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33709 p hg
    simpa only [d295403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d295403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33711 (p : Pattern) (guard : d295404 p = 1) : d50040 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295403 p = 1 := by simpa only [d295404, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33710 p hg
    simpa only [d295404, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295404, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32143 p hg
    simpa only [d295404, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33712 (p : Pattern) (guard : d295405 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295405, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d295405, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295404 p = 1 := by simpa only [d295405, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33711 p hg
    simpa only [d295405, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33713 (p : Pattern) (guard : d295406 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295400 p = 1 := by simpa only [d295406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33707 p hg
    simpa only [d295406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d295406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33714 (p : Pattern) (guard : d295407 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295401 p = 1 := by simpa only [d295407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33708 p hg
    simpa only [d295407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295406 p = 1 := by simpa only [d295407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33713 p hg
    simpa only [d295407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33715 (p : Pattern) (guard : d295408 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295407 p = 1 := by simpa only [d295408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33714 p hg
    simpa only [d295408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d295408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33716 (p : Pattern) (guard : d295409 p = 1) : d50040 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295408 p = 1 := by simpa only [d295409, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33715 p hg
    simpa only [d295409, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295409, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32143 p hg
    simpa only [d295409, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33717 (p : Pattern) (guard : d295410 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295410, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d295410, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295409 p = 1 := by simpa only [d295410, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33716 p hg
    simpa only [d295410, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33718 (p : Pattern) (guard : d295411 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295405 p = 1 := by simpa only [d295411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33712 p hg
    simpa only [d295411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295410 p = 1 := by simpa only [d295411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33717 p hg
    simpa only [d295411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33719 (p : Pattern) (guard : d295412 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295411 p = 1 := by simpa only [d295412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33718 p hg
    simpa only [d295412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33720 (p : Pattern) (guard : d295413 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295412 p = 1 := by simpa only [d295413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33719 p hg
    simpa only [d295413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33721 (p : Pattern) (guard : d295414 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295413 p = 1 := by simpa only [d295414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33720 p hg
    simpa only [d295414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33722 (p : Pattern) (guard : d295415 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295406 p = 1 := by simpa only [d295415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33713 p hg
    simpa only [d295415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d295415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33723 (p : Pattern) (guard : d295416 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295415 p = 1 := by simpa only [d295416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33722 p hg
    simpa only [d295416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d295416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33724 (p : Pattern) (guard : d295417 p = 1) : d50040 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295416 p = 1 := by simpa only [d295417, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33723 p hg
    simpa only [d295417, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295417, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32143 p hg
    simpa only [d295417, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33725 (p : Pattern) (guard : d295418 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295418, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d295418, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295417 p = 1 := by simpa only [d295418, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33724 p hg
    simpa only [d295418, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33726 (p : Pattern) (guard : d295419 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295410 p = 1 := by simpa only [d295419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33717 p hg
    simpa only [d295419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295418 p = 1 := by simpa only [d295419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33725 p hg
    simpa only [d295419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33727 (p : Pattern) (guard : d295420 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295419 p = 1 := by simpa only [d295420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33726 p hg
    simpa only [d295420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33728 (p : Pattern) (guard : d295421 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295420 p = 1 := by simpa only [d295421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33727 p hg
    simpa only [d295421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33729 (p : Pattern) (guard : d295422 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295421 p = 1 := by simpa only [d295422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33728 p hg
    simpa only [d295422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33730 (p : Pattern) (guard : d295423 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295414 p = 1 := by simpa only [d295423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33721 p hg
    simpa only [d295423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295422 p = 1 := by simpa only [d295423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33729 p hg
    simpa only [d295423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33731 (p : Pattern) (guard : d295424 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d295423 p = 1 := by simpa only [d295424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33730 p hg
    simpa only [d295424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33732 (p : Pattern) (guard : d295425 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d295387 p = 1 := by simpa only [d295425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33693 p hg
    simpa only [d295425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32101 p hg
    simpa only [d295425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33733 (p : Pattern) (guard : d295426 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295425 p = 1 := by simpa only [d295426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33732 p hg
    simpa only [d295426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32101 p hg
    simpa only [d295426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33734 (p : Pattern) (guard : d295427 p = 1) : d50037 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295427, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32100 p hg
    simpa only [d295427, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295426 p = 1 := by simpa only [d295427, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33733 p hg
    simpa only [d295427, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33735 (p : Pattern) (guard : d295428 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295428, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32099 p hg
    simpa only [d295428, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295427 p = 1 := by simpa only [d295428, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33734 p hg
    simpa only [d295428, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33736 (p : Pattern) (guard : d295429 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295428 p = 1 := by simpa only [d295429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33735 p hg
    simpa only [d295429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d295429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33737 (p : Pattern) (guard : d295430 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295401 p = 1 := by simpa only [d295430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33708 p hg
    simpa only [d295430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295429 p = 1 := by simpa only [d295430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33736 p hg
    simpa only [d295430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33738 (p : Pattern) (guard : d295431 p = 1) : d50038 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295430 p = 1 := by simpa only [d295431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33737 p hg
    simpa only [d295431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32139 p hg
    simpa only [d295431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33739 (p : Pattern) (guard : d295432 p = 1) : d50040 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295431 p = 1 := by simpa only [d295432, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33738 p hg
    simpa only [d295432, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295432, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32143 p hg
    simpa only [d295432, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33740 (p : Pattern) (guard : d295433 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295433, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d295433, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295432 p = 1 := by simpa only [d295433, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33739 p hg
    simpa only [d295433, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33741 (p : Pattern) (guard : d295434 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295433 p = 1 := by simpa only [d295434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33740 p hg
    simpa only [d295434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33742 (p : Pattern) (guard : d295435 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295434 p = 1 := by simpa only [d295435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33741 p hg
    simpa only [d295435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33743 (p : Pattern) (guard : d295436 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295435 p = 1 := by simpa only [d295436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33742 p hg
    simpa only [d295436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33744 (p : Pattern) (guard : d295437 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295436 p = 1 := by simpa only [d295437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33743 p hg
    simpa only [d295437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33745 (p : Pattern) (guard : d295438 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295437 p = 1 := by simpa only [d295438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33744 p hg
    simpa only [d295438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33746 (p : Pattern) (guard : d295439 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d295438 p = 1 := by simpa only [d295439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33745 p hg
    simpa only [d295439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33747 (p : Pattern) (guard : d295440 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295424 p = 1 := by simpa only [d295440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33731 p hg
    simpa only [d295440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295439 p = 1 := by simpa only [d295440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33746 p hg
    simpa only [d295440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33748 (p : Pattern) (guard : d295441 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295440 p = 1 := by simpa only [d295441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33747 p hg
    simpa only [d295441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare33749 (p : Pattern) (guard : d295442 p = 1) : d50041 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32098 p hg
    simpa only [d295442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295441 p = 1 := by simpa only [d295442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33748 p hg
    simpa only [d295442, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
