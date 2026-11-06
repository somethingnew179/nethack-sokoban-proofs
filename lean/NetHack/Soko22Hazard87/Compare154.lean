import NetHack.Soko22Hazard87.Compare153
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare38500 (p : Pattern) (guard : d317447 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317446 p = 1 := by simpa only [d317447, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38499 p hg
    simpa only [d317447, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317447, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37844 p hg
    simpa only [d317447, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38501 (p : Pattern) (guard : d317448 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317442 p = 1 := by simpa only [d317448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38495 p hg
    simpa only [d317448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317447 p = 1 := by simpa only [d317448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38500 p hg
    simpa only [d317448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38502 (p : Pattern) (guard : d317449 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317432 p = 1 := by simpa only [d317449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38485 p hg
    simpa only [d317449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37846 p hg
    simpa only [d317449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38503 (p : Pattern) (guard : d317450 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317448 p = 1 := by simpa only [d317450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38501 p hg
    simpa only [d317450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317449 p = 1 := by simpa only [d317450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38502 p hg
    simpa only [d317450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38504 (p : Pattern) (guard : d317451 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317434 p = 1 := by simpa only [d317451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38487 p hg
    simpa only [d317451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317450 p = 1 := by simpa only [d317451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38503 p hg
    simpa only [d317451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38505 (p : Pattern) (guard : d317452 p = 1) : d50227 p ≤ (2 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317452, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37822 p hg
    simpa only [d317452, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317451 p = 1 := by simpa only [d317452, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38504 p hg
    simpa only [d317452, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38506 (p : Pattern) (guard : d317453 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317453, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37821 p hg
    simpa only [d317453, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317452 p = 1 := by simpa only [d317453, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38505 p hg
    simpa only [d317453, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38507 (p : Pattern) (guard : d317454 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317447 p = 1 := by simpa only [d317454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38500 p hg
    simpa only [d317454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37846 p hg
    simpa only [d317454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38508 (p : Pattern) (guard : d317455 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317454 p = 1 := by simpa only [d317455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38507 p hg
    simpa only [d317455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37846 p hg
    simpa only [d317455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38509 (p : Pattern) (guard : d317456 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317450 p = 1 := by simpa only [d317456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38503 p hg
    simpa only [d317456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317455 p = 1 := by simpa only [d317456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38508 p hg
    simpa only [d317456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38510 (p : Pattern) (guard : d317457 p = 1) : d50227 p ≤ (2 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317457, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37822 p hg
    simpa only [d317457, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317456 p = 1 := by simpa only [d317457, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38509 p hg
    simpa only [d317457, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38511 (p : Pattern) (guard : d317458 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317458, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37821 p hg
    simpa only [d317458, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317457 p = 1 := by simpa only [d317458, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38510 p hg
    simpa only [d317458, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38512 (p : Pattern) (guard : d317459 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317453 p = 1 := by simpa only [d317459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38506 p hg
    simpa only [d317459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317458 p = 1 := by simpa only [d317459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38511 p hg
    simpa only [d317459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38513 (p : Pattern) (guard : d317460 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317458 p = 1 := by simpa only [d317460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38511 p hg
    simpa only [d317460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37852 p hg
    simpa only [d317460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38514 (p : Pattern) (guard : d317461 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317459 p = 1 := by simpa only [d317461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38512 p hg
    simpa only [d317461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317460 p = 1 := by simpa only [d317461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38513 p hg
    simpa only [d317461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38515 (p : Pattern) (guard : d317462 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317461 p = 1 := by simpa only [d317462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38514 p hg
    simpa only [d317462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37852 p hg
    simpa only [d317462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38516 (p : Pattern) (guard : d317463 p = 1) : d50272 p ≤ (2 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317462 p = 1 := by simpa only [d317463, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38515 p hg
    simpa only [d317463, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317463, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37856 p hg
    simpa only [d317463, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38517 (p : Pattern) (guard : d317464 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317464, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37820 p hg
    simpa only [d317464, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317463 p = 1 := by simpa only [d317464, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38516 p hg
    simpa only [d317464, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38518 (p : Pattern) (guard : d317465 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317460 p = 1 := by simpa only [d317465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38513 p hg
    simpa only [d317465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37852 p hg
    simpa only [d317465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38519 (p : Pattern) (guard : d317466 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317465 p = 1 := by simpa only [d317466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38518 p hg
    simpa only [d317466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37852 p hg
    simpa only [d317466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38520 (p : Pattern) (guard : d317467 p = 1) : d50272 p ≤ (2 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317466 p = 1 := by simpa only [d317467, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38519 p hg
    simpa only [d317467, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317467, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37856 p hg
    simpa only [d317467, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38521 (p : Pattern) (guard : d317468 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317468, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37820 p hg
    simpa only [d317468, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317467 p = 1 := by simpa only [d317468, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38520 p hg
    simpa only [d317468, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38522 (p : Pattern) (guard : d317469 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317464 p = 1 := by simpa only [d317469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38517 p hg
    simpa only [d317469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317468 p = 1 := by simpa only [d317469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38521 p hg
    simpa only [d317469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38523 (p : Pattern) (guard : d317470 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317469 p = 1 := by simpa only [d317470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38522 p hg
    simpa only [d317470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38524 (p : Pattern) (guard : d317471 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317470 p = 1 := by simpa only [d317471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38523 p hg
    simpa only [d317471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38525 (p : Pattern) (guard : d317472 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317471 p = 1 := by simpa only [d317472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38524 p hg
    simpa only [d317472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38526 (p : Pattern) (guard : d317473 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317468 p = 1 := by simpa only [d317473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38521 p hg
    simpa only [d317473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38527 (p : Pattern) (guard : d317474 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317473 p = 1 := by simpa only [d317474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38526 p hg
    simpa only [d317474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38528 (p : Pattern) (guard : d317475 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317474 p = 1 := by simpa only [d317475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38527 p hg
    simpa only [d317475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38529 (p : Pattern) (guard : d317476 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317475 p = 1 := by simpa only [d317476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38528 p hg
    simpa only [d317476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38530 (p : Pattern) (guard : d317477 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317472 p = 1 := by simpa only [d317477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38525 p hg
    simpa only [d317477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317476 p = 1 := by simpa only [d317477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38529 p hg
    simpa only [d317477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38531 (p : Pattern) (guard : d317478 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317477 p = 1 := by simpa only [d317478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38530 p hg
    simpa only [d317478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38532 (p : Pattern) (guard : d317479 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317478 p = 1 := by simpa only [d317479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38531 p hg
    simpa only [d317479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38533 (p : Pattern) (guard : d317480 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317479 p = 1 := by simpa only [d317480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38532 p hg
    simpa only [d317480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38534 (p : Pattern) (guard : d317481 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317480 p = 1 := by simpa only [d317481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38533 p hg
    simpa only [d317481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38535 (p : Pattern) (guard : d317482 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317482, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d317482, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317481 p = 1 := by simpa only [d317482, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38534 p hg
    simpa only [d317482, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38536 (p : Pattern) (guard : d317453 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317453, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37870 p hg
    simpa only [d317453, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317452 p = 1 := by simpa only [d317453, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38505 p hg
    simpa only [d317453, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38537 (p : Pattern) (guard : d317458 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317458, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37870 p hg
    simpa only [d317458, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317457 p = 1 := by simpa only [d317458, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38510 p hg
    simpa only [d317458, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38538 (p : Pattern) (guard : d317459 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317453 p = 1 := by simpa only [d317459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38536 p hg
    simpa only [d317459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317458 p = 1 := by simpa only [d317459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38537 p hg
    simpa only [d317459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38539 (p : Pattern) (guard : d317460 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317458 p = 1 := by simpa only [d317460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38537 p hg
    simpa only [d317460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37872 p hg
    simpa only [d317460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38540 (p : Pattern) (guard : d317461 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317459 p = 1 := by simpa only [d317461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38538 p hg
    simpa only [d317461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317460 p = 1 := by simpa only [d317461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38539 p hg
    simpa only [d317461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38541 (p : Pattern) (guard : d317462 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317461 p = 1 := by simpa only [d317462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38540 p hg
    simpa only [d317462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37872 p hg
    simpa only [d317462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38542 (p : Pattern) (guard : d317463 p = 1) : d50250 p ≤ (2 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317462 p = 1 := by simpa only [d317463, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38541 p hg
    simpa only [d317463, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317463, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37856 p hg
    simpa only [d317463, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38543 (p : Pattern) (guard : d317464 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317464, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37869 p hg
    simpa only [d317464, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317463 p = 1 := by simpa only [d317464, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38542 p hg
    simpa only [d317464, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38544 (p : Pattern) (guard : d317465 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317460 p = 1 := by simpa only [d317465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38539 p hg
    simpa only [d317465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37872 p hg
    simpa only [d317465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38545 (p : Pattern) (guard : d317466 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317465 p = 1 := by simpa only [d317466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38544 p hg
    simpa only [d317466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37872 p hg
    simpa only [d317466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38546 (p : Pattern) (guard : d317467 p = 1) : d50250 p ≤ (2 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317466 p = 1 := by simpa only [d317467, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38545 p hg
    simpa only [d317467, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317467, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37856 p hg
    simpa only [d317467, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38547 (p : Pattern) (guard : d317468 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317468, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37869 p hg
    simpa only [d317468, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317467 p = 1 := by simpa only [d317468, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38546 p hg
    simpa only [d317468, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38548 (p : Pattern) (guard : d317469 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317464 p = 1 := by simpa only [d317469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38543 p hg
    simpa only [d317469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317468 p = 1 := by simpa only [d317469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38547 p hg
    simpa only [d317469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38549 (p : Pattern) (guard : d317470 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317469 p = 1 := by simpa only [d317470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38548 p hg
    simpa only [d317470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d317470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38550 (p : Pattern) (guard : d317471 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317470 p = 1 := by simpa only [d317471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38549 p hg
    simpa only [d317471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d317471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38551 (p : Pattern) (guard : d317472 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d317472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317471 p = 1 := by simpa only [d317472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38550 p hg
    simpa only [d317472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38552 (p : Pattern) (guard : d317473 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317468 p = 1 := by simpa only [d317473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38547 p hg
    simpa only [d317473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d317473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38553 (p : Pattern) (guard : d317474 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317473 p = 1 := by simpa only [d317474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38552 p hg
    simpa only [d317474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d317474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38554 (p : Pattern) (guard : d317475 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317474 p = 1 := by simpa only [d317475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38553 p hg
    simpa only [d317475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d317475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38555 (p : Pattern) (guard : d317476 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d317476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317475 p = 1 := by simpa only [d317476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38554 p hg
    simpa only [d317476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38556 (p : Pattern) (guard : d317477 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317472 p = 1 := by simpa only [d317477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38551 p hg
    simpa only [d317477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317476 p = 1 := by simpa only [d317477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38555 p hg
    simpa only [d317477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38557 (p : Pattern) (guard : d317478 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d317478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317477 p = 1 := by simpa only [d317478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38556 p hg
    simpa only [d317478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38558 (p : Pattern) (guard : d317479 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317478 p = 1 := by simpa only [d317479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38557 p hg
    simpa only [d317479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d317479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38559 (p : Pattern) (guard : d317480 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d317480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317479 p = 1 := by simpa only [d317480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38558 p hg
    simpa only [d317480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38560 (p : Pattern) (guard : d317481 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d317481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317480 p = 1 := by simpa only [d317481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38559 p hg
    simpa only [d317481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38561 (p : Pattern) (guard : d317485 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317471 p = 1 := by simpa only [d317485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38524 p hg
    simpa only [d317485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38562 (p : Pattern) (guard : d317486 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317475 p = 1 := by simpa only [d317486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38528 p hg
    simpa only [d317486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38563 (p : Pattern) (guard : d317487 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317485 p = 1 := by simpa only [d317487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38561 p hg
    simpa only [d317487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317486 p = 1 := by simpa only [d317487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38562 p hg
    simpa only [d317487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38564 (p : Pattern) (guard : d317488 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317487 p = 1 := by simpa only [d317488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38563 p hg
    simpa only [d317488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38565 (p : Pattern) (guard : d317489 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317488 p = 1 := by simpa only [d317489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38564 p hg
    simpa only [d317489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38566 (p : Pattern) (guard : d317490 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317489 p = 1 := by simpa only [d317490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38565 p hg
    simpa only [d317490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38567 (p : Pattern) (guard : d317491 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317490 p = 1 := by simpa only [d317491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38566 p hg
    simpa only [d317491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38568 (p : Pattern) (guard : d317492 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d317481 p = 1 := by simpa only [d317492, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38560 p hg
    simpa only [d317492, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317491 p = 1 := by simpa only [d317492, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38567 p hg
    simpa only [d317492, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38569 (p : Pattern) (guard : d317493 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d317482 p = 1 := by simpa only [d317493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38535 p hg
    simpa only [d317493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317492 p = 1 := by simpa only [d317493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38568 p hg
    simpa only [d317493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38570 (p : Pattern) (guard : d317494 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d317493 p = 1 := by simpa only [d317494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38569 p hg
    simpa only [d317494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37817 p hg
    simpa only [d317494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38571 (p : Pattern) (guard : d318416 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d317494 p = 1 := by simpa only [d318416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38570 p hg
    simpa only [d318416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37817 p hg
    simpa only [d318416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38572 (p : Pattern) (guard : d318417 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37817 p hg
    simpa only [d318417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318416 p = 1 := by simpa only [d318417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38571 p hg
    simpa only [d318417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38573 (p : Pattern) (guard : d316353 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37912 p hg
    simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286613 p = 1 := by simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38283 p hg
    simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38574 (p : Pattern) (guard : d825 p = 1) : d47706 p ≤ (2 : Int) + d47706 p := by
  omega
theorem compare38575 (p : Pattern) (guard : d5121 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d825 p = 1 := by simpa only [d5121, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38574 p hg
    simpa only [d5121, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5121, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37906 p hg
    simpa only [d5121, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38576 (p : Pattern) (guard : d34352 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37904 p hg
    simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5121 p = 1 := by simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38575 p hg
    simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38577 (p : Pattern) (guard : d34353 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d34352 p = 1 := by simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38576 p hg
    simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37904 p hg
    simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38578 (p : Pattern) (guard : d34354 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d34353 p = 1 := by simpa only [d34354, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38577 p hg
    simpa only [d34354, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34354, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37910 p hg
    simpa only [d34354, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38579 (p : Pattern) (guard : d316354 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d34354 p = 1 := by simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38578 p hg
    simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316230 p = 1 := by simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38289 p hg
    simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38580 (p : Pattern) (guard : d316355 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316353 p = 1 := by simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38573 p hg
    simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316354 p = 1 := by simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38579 p hg
    simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38581 (p : Pattern) (guard : d316356 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316355 p = 1 := by simpa only [d316356, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38580 p hg
    simpa only [d316356, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316356, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37915 p hg
    simpa only [d316356, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38582 (p : Pattern) (guard : d40149 p = 1) : d47706 p ≤ (2 : Int) + d47706 p := by
  omega
theorem compare38583 (p : Pattern) (guard : d317407 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d40149 p = 1 := by simpa only [d317407, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38582 p hg
    simpa only [d317407, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317407, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37906 p hg
    simpa only [d317407, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38584 (p : Pattern) (guard : d317408 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37904 p hg
    simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317407 p = 1 := by simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38583 p hg
    simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38585 (p : Pattern) (guard : d317409 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d317408 p = 1 := by simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38584 p hg
    simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37904 p hg
    simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38586 (p : Pattern) (guard : d317410 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d317409 p = 1 := by simpa only [d317410, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38585 p hg
    simpa only [d317410, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317410, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37910 p hg
    simpa only [d317410, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38587 (p : Pattern) (guard : d317411 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d286613 p = 1 := by simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38283 p hg
    simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317410 p = 1 := by simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38586 p hg
    simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38588 (p : Pattern) (guard : d317412 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317411 p = 1 := by simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38587 p hg
    simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316231 p = 1 := by simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38290 p hg
    simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38589 (p : Pattern) (guard : d317413 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317412 p = 1 := by simpa only [d317413, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38588 p hg
    simpa only [d317413, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317413, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37915 p hg
    simpa only [d317413, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38590 (p : Pattern) (guard : d317414 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316356 p = 1 := by simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38581 p hg
    simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317413 p = 1 := by simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38589 p hg
    simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38591 (p : Pattern) (guard : d317415 p = 1) : d50362 p ≤ (2 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317414 p = 1 := by simpa only [d317415, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38590 p hg
    simpa only [d317415, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317415, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317415, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38592 (p : Pattern) (guard : d317416 p = 1) : d50363 p ≤ (2 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317415 p = 1 := by simpa only [d317416, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38591 p hg
    simpa only [d317416, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317416, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317416, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38593 (p : Pattern) (guard : d317417 p = 1) : d50364 p ≤ (2 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317417, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37903 p hg
    simpa only [d317417, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317416 p = 1 := by simpa only [d317417, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38592 p hg
    simpa only [d317417, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38594 (p : Pattern) (guard : d317418 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317417 p = 1 := by simpa only [d317418, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38593 p hg
    simpa only [d317418, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317418, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37924 p hg
    simpa only [d317418, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38595 (p : Pattern) (guard : d1540 p = 1) : d47706 p ≤ (2 : Int) + d47706 p := by
  omega
theorem compare38596 (p : Pattern) (guard : d1541 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1540 p = 1 := by simpa only [d1541, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38595 p hg
    simpa only [d1541, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1541, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37906 p hg
    simpa only [d1541, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38597 (p : Pattern) (guard : d258089 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37904 p hg
    simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1541 p = 1 := by simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38596 p hg
    simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38598 (p : Pattern) (guard : d316362 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258089 p = 1 := by simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38597 p hg
    simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37904 p hg
    simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38599 (p : Pattern) (guard : d316363 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d316362 p = 1 := by simpa only [d316363, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38598 p hg
    simpa only [d316363, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316363, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37910 p hg
    simpa only [d316363, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38600 (p : Pattern) (guard : d316364 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316363 p = 1 := by simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38599 p hg
    simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37911 p hg
    simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38601 (p : Pattern) (guard : d316365 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316364 p = 1 := by simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38600 p hg
    simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37912 p hg
    simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38602 (p : Pattern) (guard : d316366 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316365 p = 1 := by simpa only [d316366, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38601 p hg
    simpa only [d316366, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316366, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37915 p hg
    simpa only [d316366, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38603 (p : Pattern) (guard : d317419 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317413 p = 1 := by simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38589 p hg
    simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316366 p = 1 := by simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38602 p hg
    simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38604 (p : Pattern) (guard : d317420 p = 1) : d50362 p ≤ (2 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317419 p = 1 := by simpa only [d317420, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38603 p hg
    simpa only [d317420, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317420, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317420, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38605 (p : Pattern) (guard : d317421 p = 1) : d50363 p ≤ (2 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317420 p = 1 := by simpa only [d317421, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38604 p hg
    simpa only [d317421, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317421, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317421, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38606 (p : Pattern) (guard : d317422 p = 1) : d50364 p ≤ (2 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317422, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37903 p hg
    simpa only [d317422, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317421 p = 1 := by simpa only [d317422, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38605 p hg
    simpa only [d317422, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38607 (p : Pattern) (guard : d317423 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317422 p = 1 := by simpa only [d317423, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38606 p hg
    simpa only [d317423, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317423, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37924 p hg
    simpa only [d317423, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38608 (p : Pattern) (guard : d317424 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317418 p = 1 := by simpa only [d317424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38594 p hg
    simpa only [d317424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317423 p = 1 := by simpa only [d317424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38607 p hg
    simpa only [d317424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38609 (p : Pattern) (guard : d316373 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d286613 p = 1 := by simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38283 p hg
    simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316363 p = 1 := by simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38599 p hg
    simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38610 (p : Pattern) (guard : d316374 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316373 p = 1 := by simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38609 p hg
    simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37912 p hg
    simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38611 (p : Pattern) (guard : d316375 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316374 p = 1 := by simpa only [d316375, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38610 p hg
    simpa only [d316375, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316375, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37915 p hg
    simpa only [d316375, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38612 (p : Pattern) (guard : d316376 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316375 p = 1 := by simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38611 p hg
    simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316366 p = 1 := by simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38602 p hg
    simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38613 (p : Pattern) (guard : d316377 p = 1) : d50362 p ≤ (2 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316376 p = 1 := by simpa only [d316377, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38612 p hg
    simpa only [d316377, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316377, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d316377, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38614 (p : Pattern) (guard : d316378 p = 1) : d50363 p ≤ (2 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316377 p = 1 := by simpa only [d316378, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38613 p hg
    simpa only [d316378, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316378, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d316378, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38615 (p : Pattern) (guard : d316379 p = 1) : d50364 p ≤ (2 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316379, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37903 p hg
    simpa only [d316379, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316378 p = 1 := by simpa only [d316379, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38614 p hg
    simpa only [d316379, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38616 (p : Pattern) (guard : d316380 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316379 p = 1 := by simpa only [d316380, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38615 p hg
    simpa only [d316380, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316380, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37924 p hg
    simpa only [d316380, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38617 (p : Pattern) (guard : d317425 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317410 p = 1 := by simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38586 p hg
    simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37911 p hg
    simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38618 (p : Pattern) (guard : d317426 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317425 p = 1 := by simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38617 p hg
    simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37913 p hg
    simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38619 (p : Pattern) (guard : d317427 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317426 p = 1 := by simpa only [d317427, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38618 p hg
    simpa only [d317427, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317427, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37915 p hg
    simpa only [d317427, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38620 (p : Pattern) (guard : d317428 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317427 p = 1 := by simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38619 p hg
    simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37917 p hg
    simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38621 (p : Pattern) (guard : d317429 p = 1) : d50362 p ≤ (2 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317428 p = 1 := by simpa only [d317429, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38620 p hg
    simpa only [d317429, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317429, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317429, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38622 (p : Pattern) (guard : d317430 p = 1) : d50363 p ≤ (2 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317429 p = 1 := by simpa only [d317430, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38621 p hg
    simpa only [d317430, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317430, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317430, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38623 (p : Pattern) (guard : d317431 p = 1) : d50364 p ≤ (2 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317431, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37903 p hg
    simpa only [d317431, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317430 p = 1 := by simpa only [d317431, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38622 p hg
    simpa only [d317431, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38624 (p : Pattern) (guard : d317432 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317431 p = 1 := by simpa only [d317432, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38623 p hg
    simpa only [d317432, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317432, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37924 p hg
    simpa only [d317432, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38625 (p : Pattern) (guard : d317433 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316380 p = 1 := by simpa only [d317433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38616 p hg
    simpa only [d317433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317432 p = 1 := by simpa only [d317433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38624 p hg
    simpa only [d317433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38626 (p : Pattern) (guard : d317434 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317424 p = 1 := by simpa only [d317434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38608 p hg
    simpa only [d317434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317433 p = 1 := by simpa only [d317434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38625 p hg
    simpa only [d317434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38627 (p : Pattern) (guard : d317435 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317410 p = 1 := by simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38586 p hg
    simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37912 p hg
    simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38628 (p : Pattern) (guard : d317436 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317435 p = 1 := by simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38627 p hg
    simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37913 p hg
    simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38629 (p : Pattern) (guard : d317437 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317436 p = 1 := by simpa only [d317437, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38628 p hg
    simpa only [d317437, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317437, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37915 p hg
    simpa only [d317437, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38630 (p : Pattern) (guard : d317438 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317413 p = 1 := by simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38589 p hg
    simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317437 p = 1 := by simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38629 p hg
    simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38631 (p : Pattern) (guard : d317439 p = 1) : d50362 p ≤ (2 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317438 p = 1 := by simpa only [d317439, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38630 p hg
    simpa only [d317439, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317439, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317439, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38632 (p : Pattern) (guard : d317440 p = 1) : d50363 p ≤ (2 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317439 p = 1 := by simpa only [d317440, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38631 p hg
    simpa only [d317440, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317440, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317440, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38633 (p : Pattern) (guard : d317441 p = 1) : d50364 p ≤ (2 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317441, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37903 p hg
    simpa only [d317441, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317440 p = 1 := by simpa only [d317441, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38632 p hg
    simpa only [d317441, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38634 (p : Pattern) (guard : d317442 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317441 p = 1 := by simpa only [d317442, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38633 p hg
    simpa only [d317442, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317442, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37924 p hg
    simpa only [d317442, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38635 (p : Pattern) (guard : d317443 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317437 p = 1 := by simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38629 p hg
    simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37917 p hg
    simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38636 (p : Pattern) (guard : d317444 p = 1) : d50362 p ≤ (2 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317443 p = 1 := by simpa only [d317444, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38635 p hg
    simpa only [d317444, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317444, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317444, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38637 (p : Pattern) (guard : d317445 p = 1) : d50363 p ≤ (2 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317444 p = 1 := by simpa only [d317445, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38636 p hg
    simpa only [d317445, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317445, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317445, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38638 (p : Pattern) (guard : d317446 p = 1) : d50364 p ≤ (2 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317446, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37903 p hg
    simpa only [d317446, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317445 p = 1 := by simpa only [d317446, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38637 p hg
    simpa only [d317446, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38639 (p : Pattern) (guard : d317447 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317446 p = 1 := by simpa only [d317447, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38638 p hg
    simpa only [d317447, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317447, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37924 p hg
    simpa only [d317447, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38640 (p : Pattern) (guard : d317448 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317442 p = 1 := by simpa only [d317448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38634 p hg
    simpa only [d317448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317447 p = 1 := by simpa only [d317448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38639 p hg
    simpa only [d317448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38641 (p : Pattern) (guard : d317449 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317432 p = 1 := by simpa only [d317449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38624 p hg
    simpa only [d317449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37926 p hg
    simpa only [d317449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38642 (p : Pattern) (guard : d317450 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317448 p = 1 := by simpa only [d317450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38640 p hg
    simpa only [d317450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317449 p = 1 := by simpa only [d317450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38641 p hg
    simpa only [d317450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38643 (p : Pattern) (guard : d317451 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317434 p = 1 := by simpa only [d317451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38626 p hg
    simpa only [d317451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317450 p = 1 := by simpa only [d317451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38642 p hg
    simpa only [d317451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38644 (p : Pattern) (guard : d317452 p = 1) : d50369 p ≤ (2 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317452, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37902 p hg
    simpa only [d317452, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317451 p = 1 := by simpa only [d317452, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38643 p hg
    simpa only [d317452, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38645 (p : Pattern) (guard : d317453 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317453, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37901 p hg
    simpa only [d317453, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317452 p = 1 := by simpa only [d317453, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38644 p hg
    simpa only [d317453, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38646 (p : Pattern) (guard : d317454 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317447 p = 1 := by simpa only [d317454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38639 p hg
    simpa only [d317454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37926 p hg
    simpa only [d317454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38647 (p : Pattern) (guard : d317455 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317454 p = 1 := by simpa only [d317455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38646 p hg
    simpa only [d317455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37926 p hg
    simpa only [d317455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38648 (p : Pattern) (guard : d317456 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317450 p = 1 := by simpa only [d317456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38642 p hg
    simpa only [d317456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317455 p = 1 := by simpa only [d317456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38647 p hg
    simpa only [d317456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38649 (p : Pattern) (guard : d317457 p = 1) : d50369 p ≤ (2 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317457, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37902 p hg
    simpa only [d317457, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317456 p = 1 := by simpa only [d317457, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38648 p hg
    simpa only [d317457, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38650 (p : Pattern) (guard : d317458 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317458, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37901 p hg
    simpa only [d317458, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317457 p = 1 := by simpa only [d317458, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38649 p hg
    simpa only [d317458, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38651 (p : Pattern) (guard : d317459 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317453 p = 1 := by simpa only [d317459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38645 p hg
    simpa only [d317459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317458 p = 1 := by simpa only [d317459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38650 p hg
    simpa only [d317459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38652 (p : Pattern) (guard : d317460 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317458 p = 1 := by simpa only [d317460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38650 p hg
    simpa only [d317460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37932 p hg
    simpa only [d317460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38653 (p : Pattern) (guard : d317461 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317459 p = 1 := by simpa only [d317461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38651 p hg
    simpa only [d317461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317460 p = 1 := by simpa only [d317461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38652 p hg
    simpa only [d317461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38654 (p : Pattern) (guard : d317462 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317461 p = 1 := by simpa only [d317462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38653 p hg
    simpa only [d317462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37932 p hg
    simpa only [d317462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38655 (p : Pattern) (guard : d317463 p = 1) : d50387 p ≤ (2 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317462 p = 1 := by simpa only [d317463, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38654 p hg
    simpa only [d317463, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317463, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37936 p hg
    simpa only [d317463, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38656 (p : Pattern) (guard : d317464 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317464, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37900 p hg
    simpa only [d317464, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317463 p = 1 := by simpa only [d317464, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38655 p hg
    simpa only [d317464, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38657 (p : Pattern) (guard : d317465 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317460 p = 1 := by simpa only [d317465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38652 p hg
    simpa only [d317465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37932 p hg
    simpa only [d317465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38658 (p : Pattern) (guard : d317466 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317465 p = 1 := by simpa only [d317466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38657 p hg
    simpa only [d317466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37932 p hg
    simpa only [d317466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38659 (p : Pattern) (guard : d317467 p = 1) : d50387 p ≤ (2 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317466 p = 1 := by simpa only [d317467, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38658 p hg
    simpa only [d317467, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317467, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37936 p hg
    simpa only [d317467, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38660 (p : Pattern) (guard : d317468 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317468, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37900 p hg
    simpa only [d317468, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317467 p = 1 := by simpa only [d317468, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38659 p hg
    simpa only [d317468, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38661 (p : Pattern) (guard : d317469 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317464 p = 1 := by simpa only [d317469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38656 p hg
    simpa only [d317469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317468 p = 1 := by simpa only [d317469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38660 p hg
    simpa only [d317469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38662 (p : Pattern) (guard : d317470 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317469 p = 1 := by simpa only [d317470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38661 p hg
    simpa only [d317470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d317470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38663 (p : Pattern) (guard : d317471 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317470 p = 1 := by simpa only [d317471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38662 p hg
    simpa only [d317471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d317471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38664 (p : Pattern) (guard : d317485 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317471 p = 1 := by simpa only [d317485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38663 p hg
    simpa only [d317485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d317485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38665 (p : Pattern) (guard : d317473 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317468 p = 1 := by simpa only [d317473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38660 p hg
    simpa only [d317473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d317473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38666 (p : Pattern) (guard : d317474 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317473 p = 1 := by simpa only [d317474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38665 p hg
    simpa only [d317474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d317474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38667 (p : Pattern) (guard : d317475 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317474 p = 1 := by simpa only [d317475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38666 p hg
    simpa only [d317475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d317475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38668 (p : Pattern) (guard : d317486 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317475 p = 1 := by simpa only [d317486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38667 p hg
    simpa only [d317486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d317486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38669 (p : Pattern) (guard : d317487 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317485 p = 1 := by simpa only [d317487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38664 p hg
    simpa only [d317487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317486 p = 1 := by simpa only [d317487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38668 p hg
    simpa only [d317487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38670 (p : Pattern) (guard : d317488 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d317488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317487 p = 1 := by simpa only [d317488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38669 p hg
    simpa only [d317488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38671 (p : Pattern) (guard : d317489 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317488 p = 1 := by simpa only [d317489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38670 p hg
    simpa only [d317489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d317489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38672 (p : Pattern) (guard : d317490 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d317490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317489 p = 1 := by simpa only [d317490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38671 p hg
    simpa only [d317490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38673 (p : Pattern) (guard : d317491 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d317491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317490 p = 1 := by simpa only [d317491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38672 p hg
    simpa only [d317491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38674 (p : Pattern) (guard : d318418 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318418, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d318418, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317491 p = 1 := by simpa only [d318418, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38673 p hg
    simpa only [d318418, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38675 (p : Pattern) (guard : d318419 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37898 p hg
    simpa only [d318419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318418 p = 1 := by simpa only [d318419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38674 p hg
    simpa only [d318419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38676 (p : Pattern) (guard : d318420 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d318419 p = 1 := by simpa only [d318420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38675 p hg
    simpa only [d318420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37898 p hg
    simpa only [d318420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38677 (p : Pattern) (guard : d318421 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d318420 p = 1 := by simpa only [d318421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38676 p hg
    simpa only [d318421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37898 p hg
    simpa only [d318421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38678 (p : Pattern) (guard : d318422 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d318421 p = 1 := by simpa only [d318422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38677 p hg
    simpa only [d318422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37898 p hg
    simpa only [d318422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38679 (p : Pattern) (guard : d318423 p = 1) : d50390 p ≤ (2 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d318417 p = 1 := by simpa only [d318423, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38572 p hg
    simpa only [d318423, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318422 p = 1 := by simpa only [d318423, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38678 p hg
    simpa only [d318423, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38680 (p : Pattern) (guard : d316353 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37967 p hg
    simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286613 p = 1 := by simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38344 p hg
    simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38681 (p : Pattern) (guard : d825 p = 1) : d47630 p ≤ (2 : Int) + d47630 p := by
  omega
theorem compare38682 (p : Pattern) (guard : d5121 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d825 p = 1 := by simpa only [d5121, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38681 p hg
    simpa only [d5121, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5121, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37961 p hg
    simpa only [d5121, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38683 (p : Pattern) (guard : d34352 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37959 p hg
    simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5121 p = 1 := by simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38682 p hg
    simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38684 (p : Pattern) (guard : d34353 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d34352 p = 1 := by simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38683 p hg
    simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37959 p hg
    simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38685 (p : Pattern) (guard : d34354 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d34353 p = 1 := by simpa only [d34354, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38684 p hg
    simpa only [d34354, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34354, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37965 p hg
    simpa only [d34354, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38686 (p : Pattern) (guard : d316354 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d34354 p = 1 := by simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38685 p hg
    simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316230 p = 1 := by simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38350 p hg
    simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38687 (p : Pattern) (guard : d316355 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316353 p = 1 := by simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38680 p hg
    simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316354 p = 1 := by simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38686 p hg
    simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38688 (p : Pattern) (guard : d316356 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316355 p = 1 := by simpa only [d316356, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38687 p hg
    simpa only [d316356, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316356, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37970 p hg
    simpa only [d316356, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38689 (p : Pattern) (guard : d40149 p = 1) : d47630 p ≤ (2 : Int) + d47630 p := by
  omega
theorem compare38690 (p : Pattern) (guard : d317407 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d40149 p = 1 := by simpa only [d317407, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38689 p hg
    simpa only [d317407, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317407, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37961 p hg
    simpa only [d317407, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38691 (p : Pattern) (guard : d317408 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37959 p hg
    simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317407 p = 1 := by simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38690 p hg
    simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38692 (p : Pattern) (guard : d317409 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d317408 p = 1 := by simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38691 p hg
    simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37959 p hg
    simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38693 (p : Pattern) (guard : d317410 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d317409 p = 1 := by simpa only [d317410, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38692 p hg
    simpa only [d317410, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317410, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37965 p hg
    simpa only [d317410, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38694 (p : Pattern) (guard : d317411 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d286613 p = 1 := by simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38344 p hg
    simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317410 p = 1 := by simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38693 p hg
    simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38695 (p : Pattern) (guard : d317412 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317411 p = 1 := by simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38694 p hg
    simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316231 p = 1 := by simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38351 p hg
    simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38696 (p : Pattern) (guard : d317413 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317412 p = 1 := by simpa only [d317413, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38695 p hg
    simpa only [d317413, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317413, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37970 p hg
    simpa only [d317413, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38697 (p : Pattern) (guard : d317414 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316356 p = 1 := by simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38688 p hg
    simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317413 p = 1 := by simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38696 p hg
    simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38698 (p : Pattern) (guard : d317589 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d317589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317414 p = 1 := by simpa only [d317589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38697 p hg
    simpa only [d317589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38699 (p : Pattern) (guard : d317415 p = 1) : d50420 p ≤ (2 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317414 p = 1 := by simpa only [d317415, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38451 p hg
    simpa only [d317415, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317415, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317415, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38700 (p : Pattern) (guard : d317590 p = 1) : d50421 p ≤ (2 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317589 p = 1 := by simpa only [d317590, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38698 p hg
    simpa only [d317590, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317415 p = 1 := by simpa only [d317590, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38699 p hg
    simpa only [d317590, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38701 (p : Pattern) (guard : d316353 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37984 p hg
    simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286613 p = 1 := by simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38362 p hg
    simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38702 (p : Pattern) (guard : d825 p = 1) : d47634 p ≤ (2 : Int) + d47634 p := by
  omega
theorem compare38703 (p : Pattern) (guard : d5121 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d825 p = 1 := by simpa only [d5121, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38702 p hg
    simpa only [d5121, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5121, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37978 p hg
    simpa only [d5121, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38704 (p : Pattern) (guard : d34352 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37976 p hg
    simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5121 p = 1 := by simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38703 p hg
    simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38705 (p : Pattern) (guard : d34353 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d34352 p = 1 := by simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38704 p hg
    simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37976 p hg
    simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38706 (p : Pattern) (guard : d34354 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d34353 p = 1 := by simpa only [d34354, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38705 p hg
    simpa only [d34354, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34354, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37982 p hg
    simpa only [d34354, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38707 (p : Pattern) (guard : d316354 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d34354 p = 1 := by simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38706 p hg
    simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316230 p = 1 := by simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38368 p hg
    simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38708 (p : Pattern) (guard : d316355 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316353 p = 1 := by simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38701 p hg
    simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316354 p = 1 := by simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38707 p hg
    simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38709 (p : Pattern) (guard : d316356 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316355 p = 1 := by simpa only [d316356, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38708 p hg
    simpa only [d316356, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316356, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37987 p hg
    simpa only [d316356, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38710 (p : Pattern) (guard : d40149 p = 1) : d47634 p ≤ (2 : Int) + d47634 p := by
  omega
theorem compare38711 (p : Pattern) (guard : d317407 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d40149 p = 1 := by simpa only [d317407, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38710 p hg
    simpa only [d317407, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317407, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37978 p hg
    simpa only [d317407, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38712 (p : Pattern) (guard : d317408 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37976 p hg
    simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317407 p = 1 := by simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38711 p hg
    simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38713 (p : Pattern) (guard : d317409 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d317408 p = 1 := by simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38712 p hg
    simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37976 p hg
    simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38714 (p : Pattern) (guard : d317410 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d317409 p = 1 := by simpa only [d317410, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38713 p hg
    simpa only [d317410, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317410, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37982 p hg
    simpa only [d317410, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38715 (p : Pattern) (guard : d317411 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d286613 p = 1 := by simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38362 p hg
    simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317410 p = 1 := by simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38714 p hg
    simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38716 (p : Pattern) (guard : d317412 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317411 p = 1 := by simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38715 p hg
    simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316231 p = 1 := by simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38369 p hg
    simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38717 (p : Pattern) (guard : d317413 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317412 p = 1 := by simpa only [d317413, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38716 p hg
    simpa only [d317413, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317413, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37987 p hg
    simpa only [d317413, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38718 (p : Pattern) (guard : d317414 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316356 p = 1 := by simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38709 p hg
    simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317413 p = 1 := by simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38717 p hg
    simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38719 (p : Pattern) (guard : d317415 p = 1) : d50223 p ≤ (2 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317414 p = 1 := by simpa only [d317415, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38718 p hg
    simpa only [d317415, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317415, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317415, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38720 (p : Pattern) (guard : d317416 p = 1) : d50224 p ≤ (2 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317415 p = 1 := by simpa only [d317416, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38719 p hg
    simpa only [d317416, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317416, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317416, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38721 (p : Pattern) (guard : d317591 p = 1) : d50422 p ≤ (2 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317590 p = 1 := by simpa only [d317591, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38700 p hg
    simpa only [d317591, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317416 p = 1 := by simpa only [d317591, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38720 p hg
    simpa only [d317591, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38722 (p : Pattern) (guard : d317592 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317591 p = 1 := by simpa only [d317592, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38721 p hg
    simpa only [d317592, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317592, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37994 p hg
    simpa only [d317592, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38723 (p : Pattern) (guard : d1540 p = 1) : d47630 p ≤ (2 : Int) + d47630 p := by
  omega
theorem compare38724 (p : Pattern) (guard : d1541 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1540 p = 1 := by simpa only [d1541, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38723 p hg
    simpa only [d1541, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1541, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37961 p hg
    simpa only [d1541, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38725 (p : Pattern) (guard : d258089 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37959 p hg
    simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1541 p = 1 := by simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38724 p hg
    simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38726 (p : Pattern) (guard : d316362 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258089 p = 1 := by simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38725 p hg
    simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37959 p hg
    simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38727 (p : Pattern) (guard : d316363 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d316362 p = 1 := by simpa only [d316363, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38726 p hg
    simpa only [d316363, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316363, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37965 p hg
    simpa only [d316363, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38728 (p : Pattern) (guard : d316364 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316363 p = 1 := by simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38727 p hg
    simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37966 p hg
    simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38729 (p : Pattern) (guard : d316365 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316364 p = 1 := by simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38728 p hg
    simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37967 p hg
    simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38730 (p : Pattern) (guard : d316366 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316365 p = 1 := by simpa only [d316366, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38729 p hg
    simpa only [d316366, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316366, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37970 p hg
    simpa only [d316366, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38731 (p : Pattern) (guard : d317419 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317413 p = 1 := by simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38696 p hg
    simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316366 p = 1 := by simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38730 p hg
    simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38732 (p : Pattern) (guard : d317593 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d317593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317419 p = 1 := by simpa only [d317593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38731 p hg
    simpa only [d317593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38733 (p : Pattern) (guard : d317420 p = 1) : d50420 p ≤ (2 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317419 p = 1 := by simpa only [d317420, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38464 p hg
    simpa only [d317420, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317420, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317420, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38734 (p : Pattern) (guard : d317594 p = 1) : d50421 p ≤ (2 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317593 p = 1 := by simpa only [d317594, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38732 p hg
    simpa only [d317594, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317420 p = 1 := by simpa only [d317594, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38733 p hg
    simpa only [d317594, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38735 (p : Pattern) (guard : d1540 p = 1) : d47634 p ≤ (2 : Int) + d47634 p := by
  omega
theorem compare38736 (p : Pattern) (guard : d1541 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1540 p = 1 := by simpa only [d1541, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38735 p hg
    simpa only [d1541, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1541, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37978 p hg
    simpa only [d1541, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38737 (p : Pattern) (guard : d258089 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37976 p hg
    simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1541 p = 1 := by simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38736 p hg
    simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38738 (p : Pattern) (guard : d316362 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258089 p = 1 := by simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38737 p hg
    simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37976 p hg
    simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38739 (p : Pattern) (guard : d316363 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d316362 p = 1 := by simpa only [d316363, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38738 p hg
    simpa only [d316363, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316363, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37982 p hg
    simpa only [d316363, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38740 (p : Pattern) (guard : d316364 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316363 p = 1 := by simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38739 p hg
    simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37983 p hg
    simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38741 (p : Pattern) (guard : d316365 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316364 p = 1 := by simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38740 p hg
    simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37984 p hg
    simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38742 (p : Pattern) (guard : d316366 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316365 p = 1 := by simpa only [d316366, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38741 p hg
    simpa only [d316366, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316366, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37987 p hg
    simpa only [d316366, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38743 (p : Pattern) (guard : d317419 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317413 p = 1 := by simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38717 p hg
    simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316366 p = 1 := by simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38742 p hg
    simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38744 (p : Pattern) (guard : d317420 p = 1) : d50223 p ≤ (2 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317419 p = 1 := by simpa only [d317420, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38743 p hg
    simpa only [d317420, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317420, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317420, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38745 (p : Pattern) (guard : d317421 p = 1) : d50224 p ≤ (2 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317420 p = 1 := by simpa only [d317421, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38744 p hg
    simpa only [d317421, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317421, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317421, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38746 (p : Pattern) (guard : d317595 p = 1) : d50422 p ≤ (2 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317594 p = 1 := by simpa only [d317595, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38734 p hg
    simpa only [d317595, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317421 p = 1 := by simpa only [d317595, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38745 p hg
    simpa only [d317595, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38747 (p : Pattern) (guard : d317596 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317595 p = 1 := by simpa only [d317596, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38746 p hg
    simpa only [d317596, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317596, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37994 p hg
    simpa only [d317596, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38748 (p : Pattern) (guard : d317597 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317592 p = 1 := by simpa only [d317597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38722 p hg
    simpa only [d317597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317596 p = 1 := by simpa only [d317597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38747 p hg
    simpa only [d317597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38749 (p : Pattern) (guard : d316373 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d286613 p = 1 := by simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38344 p hg
    simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316363 p = 1 := by simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38727 p hg
    simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
