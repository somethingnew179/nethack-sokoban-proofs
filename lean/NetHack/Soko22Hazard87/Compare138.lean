import NetHack.Soko22Hazard87.Compare137
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare34500 (p : Pattern) (guard : d295737 p = 1) : d50001 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d295736 p = 1 := by simpa only [d295737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34499 p hg
    simpa only [d295737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33935 p hg
    simpa only [d295737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34501 (p : Pattern) (guard : d295738 p = 1) : d50001 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d295737 p = 1 := by simpa only [d295738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34500 p hg
    simpa only [d295738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33935 p hg
    simpa only [d295738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34502 (p : Pattern) (guard : d295739 p = 1) : d50001 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d295738 p = 1 := by simpa only [d295739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34501 p hg
    simpa only [d295739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33935 p hg
    simpa only [d295739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34503 (p : Pattern) (guard : d295740 p = 1) : d50002 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d295734 p = 1 := by simpa only [d295740, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d295740, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295739 p = 1 := by simpa only [d295740, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34502 p hg
    simpa only [d295740, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34504 (p : Pattern) (guard : d1532 p = 1) : d47630 p ≤ (0 : Int) + d47630 p := by
  omega
theorem compare34505 (p : Pattern) (guard : d25764 p = 1) : d49808 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1532 p = 1 := by simpa only [d25764, d49808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34504 p hg
    simpa only [d25764, d49808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25764, d49808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34018 p hg
    simpa only [d25764, d49808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34506 (p : Pattern) (guard : d25765 p = 1) : d49808 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d25764 p = 1 := by simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34505 p hg
    simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34016 p hg
    simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34507 (p : Pattern) (guard : d25766 p = 1) : d49808 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d25765 p = 1 := by simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34506 p hg
    simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34016 p hg
    simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34508 (p : Pattern) (guard : d31739 p = 1) : d49808 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34016 p hg
    simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d25766 p = 1 := by simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34507 p hg
    simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34509 (p : Pattern) (guard : d294870 p = 1) : d49808 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34016 p hg
    simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d31739 p = 1 := by simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34508 p hg
    simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34510 (p : Pattern) (guard : d294871 p = 1) : d49831 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294870 p = 1 := by simpa only [d294871, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34509 p hg
    simpa only [d294871, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294871, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34024 p hg
    simpa only [d294871, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34511 (p : Pattern) (guard : d294872 p = 1) : d49831 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294871 p = 1 := by simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34510 p hg
    simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34015 p hg
    simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34512 (p : Pattern) (guard : d294951 p = 1) : d49831 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34015 p hg
    simpa only [d294951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294872 p = 1 := by simpa only [d294951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34511 p hg
    simpa only [d294951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34513 (p : Pattern) (guard : d294873 p = 1) : d50030 p ≤ (0 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294872 p = 1 := by simpa only [d294873, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34359 p hg
    simpa only [d294873, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294873, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33954 p hg
    simpa only [d294873, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34514 (p : Pattern) (guard : d294952 p = 1) : d50031 p ≤ (0 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294951 p = 1 := by simpa only [d294952, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34512 p hg
    simpa only [d294952, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294873 p = 1 := by simpa only [d294952, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34513 p hg
    simpa only [d294952, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34515 (p : Pattern) (guard : d1532 p = 1) : d47634 p ≤ (0 : Int) + d47634 p := by
  omega
theorem compare34516 (p : Pattern) (guard : d25764 p = 1) : d49811 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1532 p = 1 := by simpa only [d25764, d49811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34515 p hg
    simpa only [d25764, d49811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25764, d49811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34032 p hg
    simpa only [d25764, d49811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34517 (p : Pattern) (guard : d25765 p = 1) : d49811 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d25764 p = 1 := by simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34516 p hg
    simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34030 p hg
    simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34518 (p : Pattern) (guard : d25766 p = 1) : d49811 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d25765 p = 1 := by simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34517 p hg
    simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34030 p hg
    simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34519 (p : Pattern) (guard : d31739 p = 1) : d49811 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34030 p hg
    simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d25766 p = 1 := by simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34518 p hg
    simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34520 (p : Pattern) (guard : d294870 p = 1) : d49811 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34030 p hg
    simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d31739 p = 1 := by simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34519 p hg
    simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34521 (p : Pattern) (guard : d294871 p = 1) : d49857 p ≤ (0 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294870 p = 1 := by simpa only [d294871, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34520 p hg
    simpa only [d294871, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294871, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34038 p hg
    simpa only [d294871, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34522 (p : Pattern) (guard : d294872 p = 1) : d49857 p ≤ (0 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294871 p = 1 := by simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34521 p hg
    simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34040 p hg
    simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34523 (p : Pattern) (guard : d294873 p = 1) : d49865 p ≤ (0 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294872 p = 1 := by simpa only [d294873, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34522 p hg
    simpa only [d294873, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294873, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d294873, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34524 (p : Pattern) (guard : d294874 p = 1) : d49866 p ≤ (0 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294873 p = 1 := by simpa only [d294874, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34523 p hg
    simpa only [d294874, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294874, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d294874, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34525 (p : Pattern) (guard : d294953 p = 1) : d50032 p ≤ (0 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d294952 p = 1 := by simpa only [d294953, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34514 p hg
    simpa only [d294953, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294874 p = 1 := by simpa only [d294953, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34524 p hg
    simpa only [d294953, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34526 (p : Pattern) (guard : d294954 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294953 p = 1 := by simpa only [d294954, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34525 p hg
    simpa only [d294954, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294954, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34045 p hg
    simpa only [d294954, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34527 (p : Pattern) (guard : d294955 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34014 p hg
    simpa only [d294955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294954 p = 1 := by simpa only [d294955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34526 p hg
    simpa only [d294955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34528 (p : Pattern) (guard : d293903 p = 1) : d49808 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d31739 p = 1 := by simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34508 p hg
    simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34016 p hg
    simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34529 (p : Pattern) (guard : d293904 p = 1) : d49831 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d293903 p = 1 := by simpa only [d293904, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34528 p hg
    simpa only [d293904, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293904, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34024 p hg
    simpa only [d293904, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34530 (p : Pattern) (guard : d293905 p = 1) : d49831 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d293904 p = 1 := by simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34529 p hg
    simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34015 p hg
    simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34531 (p : Pattern) (guard : d294084 p = 1) : d49831 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34015 p hg
    simpa only [d294084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293905 p = 1 := by simpa only [d294084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34530 p hg
    simpa only [d294084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34532 (p : Pattern) (guard : d293906 p = 1) : d50030 p ≤ (0 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d293905 p = 1 := by simpa only [d293906, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d293906, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293906, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33954 p hg
    simpa only [d293906, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34533 (p : Pattern) (guard : d294085 p = 1) : d50031 p ≤ (0 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294084 p = 1 := by simpa only [d294085, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34531 p hg
    simpa only [d294085, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293906 p = 1 := by simpa only [d294085, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d294085, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34534 (p : Pattern) (guard : d293903 p = 1) : d49811 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d31739 p = 1 := by simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34519 p hg
    simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34030 p hg
    simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34535 (p : Pattern) (guard : d293904 p = 1) : d49857 p ≤ (0 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d293903 p = 1 := by simpa only [d293904, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34534 p hg
    simpa only [d293904, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293904, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34038 p hg
    simpa only [d293904, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34536 (p : Pattern) (guard : d293905 p = 1) : d49857 p ≤ (0 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d293904 p = 1 := by simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34535 p hg
    simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34040 p hg
    simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34537 (p : Pattern) (guard : d293906 p = 1) : d49865 p ≤ (0 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d293905 p = 1 := by simpa only [d293906, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34536 p hg
    simpa only [d293906, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293906, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d293906, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34538 (p : Pattern) (guard : d293907 p = 1) : d49866 p ≤ (0 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d293906 p = 1 := by simpa only [d293907, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34537 p hg
    simpa only [d293907, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293907, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d293907, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34539 (p : Pattern) (guard : d294086 p = 1) : d50032 p ≤ (0 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d294085 p = 1 := by simpa only [d294086, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34533 p hg
    simpa only [d294086, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293907 p = 1 := by simpa only [d294086, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34538 p hg
    simpa only [d294086, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34540 (p : Pattern) (guard : d294087 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294086 p = 1 := by simpa only [d294087, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34539 p hg
    simpa only [d294087, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294087, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34045 p hg
    simpa only [d294087, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34541 (p : Pattern) (guard : d295167 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34014 p hg
    simpa only [d295167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294087 p = 1 := by simpa only [d295167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34540 p hg
    simpa only [d295167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34542 (p : Pattern) (guard : d295168 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294955 p = 1 := by simpa only [d295168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34527 p hg
    simpa only [d295168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295167 p = 1 := by simpa only [d295168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34541 p hg
    simpa only [d295168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34543 (p : Pattern) (guard : d294098 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d294087 p = 1 := by simpa only [d294098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34540 p hg
    simpa only [d294098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34014 p hg
    simpa only [d294098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34544 (p : Pattern) (guard : d295172 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d295167 p = 1 := by simpa only [d295172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34541 p hg
    simpa only [d295172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294098 p = 1 := by simpa only [d295172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d295172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34545 (p : Pattern) (guard : d295173 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295168 p = 1 := by simpa only [d295173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34542 p hg
    simpa only [d295173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295172 p = 1 := by simpa only [d295173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34544 p hg
    simpa only [d295173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34546 (p : Pattern) (guard : d295174 p = 1) : d50037 p ≤ (0 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295174, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34013 p hg
    simpa only [d295174, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295173 p = 1 := by simpa only [d295174, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34545 p hg
    simpa only [d295174, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34547 (p : Pattern) (guard : d295175 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295175, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34012 p hg
    simpa only [d295175, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295174 p = 1 := by simpa only [d295175, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34546 p hg
    simpa only [d295175, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34548 (p : Pattern) (guard : d295177 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294098 p = 1 := by simpa only [d295177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d295177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34014 p hg
    simpa only [d295177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34549 (p : Pattern) (guard : d295178 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295172 p = 1 := by simpa only [d295178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34544 p hg
    simpa only [d295178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295177 p = 1 := by simpa only [d295178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34548 p hg
    simpa only [d295178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34550 (p : Pattern) (guard : d295179 p = 1) : d50037 p ≤ (0 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295179, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34013 p hg
    simpa only [d295179, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295178 p = 1 := by simpa only [d295179, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34549 p hg
    simpa only [d295179, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34551 (p : Pattern) (guard : d295180 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295180, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34012 p hg
    simpa only [d295180, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295179 p = 1 := by simpa only [d295180, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34550 p hg
    simpa only [d295180, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34552 (p : Pattern) (guard : d295181 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295175 p = 1 := by simpa only [d295181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34547 p hg
    simpa only [d295181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295180 p = 1 := by simpa only [d295181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34551 p hg
    simpa only [d295181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34553 (p : Pattern) (guard : d295186 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295180 p = 1 := by simpa only [d295186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34551 p hg
    simpa only [d295186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34073 p hg
    simpa only [d295186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34554 (p : Pattern) (guard : d295187 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295181 p = 1 := by simpa only [d295187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34552 p hg
    simpa only [d295187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295186 p = 1 := by simpa only [d295187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34553 p hg
    simpa only [d295187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34555 (p : Pattern) (guard : d295188 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295187 p = 1 := by simpa only [d295188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34554 p hg
    simpa only [d295188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34073 p hg
    simpa only [d295188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34556 (p : Pattern) (guard : d295189 p = 1) : d50040 p ≤ (0 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295188 p = 1 := by simpa only [d295189, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34555 p hg
    simpa only [d295189, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295189, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34077 p hg
    simpa only [d295189, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34557 (p : Pattern) (guard : d295190 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295190, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33826 p hg
    simpa only [d295190, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295189 p = 1 := by simpa only [d295190, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34556 p hg
    simpa only [d295190, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34558 (p : Pattern) (guard : d295195 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295186 p = 1 := by simpa only [d295195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34553 p hg
    simpa only [d295195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34073 p hg
    simpa only [d295195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34559 (p : Pattern) (guard : d295196 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295195 p = 1 := by simpa only [d295196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34558 p hg
    simpa only [d295196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34073 p hg
    simpa only [d295196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34560 (p : Pattern) (guard : d295197 p = 1) : d50040 p ≤ (0 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295196 p = 1 := by simpa only [d295197, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34559 p hg
    simpa only [d295197, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295197, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34077 p hg
    simpa only [d295197, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34561 (p : Pattern) (guard : d295198 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295198, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33826 p hg
    simpa only [d295198, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295197 p = 1 := by simpa only [d295198, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34560 p hg
    simpa only [d295198, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34562 (p : Pattern) (guard : d295199 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295190 p = 1 := by simpa only [d295199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34557 p hg
    simpa only [d295199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295198 p = 1 := by simpa only [d295199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34561 p hg
    simpa only [d295199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34563 (p : Pattern) (guard : d295200 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295199 p = 1 := by simpa only [d295200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34562 p hg
    simpa only [d295200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34564 (p : Pattern) (guard : d295201 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295200 p = 1 := by simpa only [d295201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34563 p hg
    simpa only [d295201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34565 (p : Pattern) (guard : d295202 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295201 p = 1 := by simpa only [d295202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34564 p hg
    simpa only [d295202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34566 (p : Pattern) (guard : d295216 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295198 p = 1 := by simpa only [d295216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34561 p hg
    simpa only [d295216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34567 (p : Pattern) (guard : d295217 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295216 p = 1 := by simpa only [d295217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34566 p hg
    simpa only [d295217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34568 (p : Pattern) (guard : d295218 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295217 p = 1 := by simpa only [d295218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34567 p hg
    simpa only [d295218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34569 (p : Pattern) (guard : d295219 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295218 p = 1 := by simpa only [d295219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34568 p hg
    simpa only [d295219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34570 (p : Pattern) (guard : d295741 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295202 p = 1 := by simpa only [d295741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34565 p hg
    simpa only [d295741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295219 p = 1 := by simpa only [d295741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34569 p hg
    simpa only [d295741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34571 (p : Pattern) (guard : d295742 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295741 p = 1 := by simpa only [d295742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34570 p hg
    simpa only [d295742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34572 (p : Pattern) (guard : d295743 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295742 p = 1 := by simpa only [d295743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34571 p hg
    simpa only [d295743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34573 (p : Pattern) (guard : d295744 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295743 p = 1 := by simpa only [d295744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34572 p hg
    simpa only [d295744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34574 (p : Pattern) (guard : d295745 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295744 p = 1 := by simpa only [d295745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34573 p hg
    simpa only [d295745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34575 (p : Pattern) (guard : d295746 p = 1) : d50042 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295746, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295746, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295745 p = 1 := by simpa only [d295746, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34574 p hg
    simpa only [d295746, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34576 (p : Pattern) (guard : d295747 p = 1) : d50042 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34010 p hg
    simpa only [d295747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295746 p = 1 := by simpa only [d295747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34575 p hg
    simpa only [d295747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34577 (p : Pattern) (guard : d295748 p = 1) : d50042 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d295747 p = 1 := by simpa only [d295748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34576 p hg
    simpa only [d295748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34010 p hg
    simpa only [d295748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34578 (p : Pattern) (guard : d295749 p = 1) : d50042 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d295748 p = 1 := by simpa only [d295749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d295749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34010 p hg
    simpa only [d295749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34579 (p : Pattern) (guard : d295750 p = 1) : d50042 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d295749 p = 1 := by simpa only [d295750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34578 p hg
    simpa only [d295750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34010 p hg
    simpa only [d295750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34580 (p : Pattern) (guard : d295751 p = 1) : d50100 p ≤ (0 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d295750 p = 1 := by simpa only [d295751, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34579 p hg
    simpa only [d295751, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295751, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34102 p hg
    simpa only [d295751, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34581 (p : Pattern) (guard : d295752 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d295740 p = 1 := by simpa only [d295752, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34503 p hg
    simpa only [d295752, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295751 p = 1 := by simpa only [d295752, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34580 p hg
    simpa only [d295752, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34582 (p : Pattern) (guard : d295753 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295752 p = 1 := by simpa only [d295753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34581 p hg
    simpa only [d295753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34583 (p : Pattern) (guard : d295754 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295753 p = 1 := by simpa only [d295754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34582 p hg
    simpa only [d295754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34584 (p : Pattern) (guard : d295755 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295754 p = 1 := by simpa only [d295755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34583 p hg
    simpa only [d295755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34585 (p : Pattern) (guard : d295756 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295755 p = 1 := by simpa only [d295756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34584 p hg
    simpa only [d295756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34586 (p : Pattern) (guard : d295757 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295756 p = 1 := by simpa only [d295757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34585 p hg
    simpa only [d295757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34587 (p : Pattern) (guard : d295758 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295757 p = 1 := by simpa only [d295758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34586 p hg
    simpa only [d295758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34588 (p : Pattern) (guard : d295759 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295758 p = 1 := by simpa only [d295759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34587 p hg
    simpa only [d295759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34589 (p : Pattern) (guard : d295760 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295759 p = 1 := by simpa only [d295760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34588 p hg
    simpa only [d295760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34590 (p : Pattern) (guard : d295761 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295760 p = 1 := by simpa only [d295761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34589 p hg
    simpa only [d295761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34591 (p : Pattern) (guard : d295762 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d295732 p = 1 := by simpa only [d295762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34351 p hg
    simpa only [d295762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295761 p = 1 := by simpa only [d295762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34590 p hg
    simpa only [d295762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34592 (p : Pattern) (guard : d2014 p = 1) : d47617 p ≤ (0 : Int) + d47617 p := by
  omega
theorem compare34593 (p : Pattern) (guard : d32701 p = 1) : d49795 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2014 p = 1 := by simpa only [d32701, d49795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34592 p hg
    simpa only [d32701, d49795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32701, d49795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33833 p hg
    simpa only [d32701, d49795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34594 (p : Pattern) (guard : d32702 p = 1) : d49795 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d32701 p = 1 := by simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34593 p hg
    simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33831 p hg
    simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34595 (p : Pattern) (guard : d32703 p = 1) : d49795 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d32702 p = 1 := by simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34594 p hg
    simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33831 p hg
    simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34596 (p : Pattern) (guard : d294185 p = 1) : d49795 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33831 p hg
    simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32703 p = 1 := by simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34595 p hg
    simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34597 (p : Pattern) (guard : d294186 p = 1) : d49795 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d294185 p = 1 := by simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34596 p hg
    simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33831 p hg
    simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34598 (p : Pattern) (guard : d294187 p = 1) : d49797 p ≤ (0 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294186 p = 1 := by simpa only [d294187, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34597 p hg
    simpa only [d294187, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294187, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33839 p hg
    simpa only [d294187, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34599 (p : Pattern) (guard : d294188 p = 1) : d49797 p ≤ (0 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294187 p = 1 := by simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34598 p hg
    simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33841 p hg
    simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34600 (p : Pattern) (guard : d294189 p = 1) : d49838 p ≤ (0 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294188 p = 1 := by simpa only [d294189, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34599 p hg
    simpa only [d294189, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294189, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33843 p hg
    simpa only [d294189, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34601 (p : Pattern) (guard : d294190 p = 1) : d49841 p ≤ (0 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294189 p = 1 := by simpa only [d294190, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34600 p hg
    simpa only [d294190, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294190, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33845 p hg
    simpa only [d294190, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34602 (p : Pattern) (guard : d294191 p = 1) : d49864 p ≤ (0 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294191, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33830 p hg
    simpa only [d294191, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294190 p = 1 := by simpa only [d294191, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34601 p hg
    simpa only [d294191, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34603 (p : Pattern) (guard : d294192 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294191 p = 1 := by simpa only [d294192, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34602 p hg
    simpa only [d294192, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294192, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33848 p hg
    simpa only [d294192, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34604 (p : Pattern) (guard : d295242 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33829 p hg
    simpa only [d295242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294192 p = 1 := by simpa only [d295242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34603 p hg
    simpa only [d295242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34605 (p : Pattern) (guard : d295243 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33829 p hg
    simpa only [d295243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295242 p = 1 := by simpa only [d295243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34604 p hg
    simpa only [d295243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34606 (p : Pattern) (guard : d294204 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d294192 p = 1 := by simpa only [d294204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34603 p hg
    simpa only [d294204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33829 p hg
    simpa only [d294204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34607 (p : Pattern) (guard : d295244 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d295242 p = 1 := by simpa only [d295244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34604 p hg
    simpa only [d295244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294204 p = 1 := by simpa only [d295244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34606 p hg
    simpa only [d295244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34608 (p : Pattern) (guard : d295245 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295243 p = 1 := by simpa only [d295245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34605 p hg
    simpa only [d295245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295244 p = 1 := by simpa only [d295245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34607 p hg
    simpa only [d295245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34609 (p : Pattern) (guard : d295246 p = 1) : d49869 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295246, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33828 p hg
    simpa only [d295246, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295245 p = 1 := by simpa only [d295246, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34608 p hg
    simpa only [d295246, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34610 (p : Pattern) (guard : d295247 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295247, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33827 p hg
    simpa only [d295247, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295246 p = 1 := by simpa only [d295247, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34609 p hg
    simpa only [d295247, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34611 (p : Pattern) (guard : d295248 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294204 p = 1 := by simpa only [d295248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34606 p hg
    simpa only [d295248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33829 p hg
    simpa only [d295248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34612 (p : Pattern) (guard : d295249 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295244 p = 1 := by simpa only [d295249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34607 p hg
    simpa only [d295249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295248 p = 1 := by simpa only [d295249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d295249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34613 (p : Pattern) (guard : d295250 p = 1) : d49869 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295250, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33828 p hg
    simpa only [d295250, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295249 p = 1 := by simpa only [d295250, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34612 p hg
    simpa only [d295250, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34614 (p : Pattern) (guard : d295251 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295251, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33827 p hg
    simpa only [d295251, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295250 p = 1 := by simpa only [d295251, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d295251, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34615 (p : Pattern) (guard : d295252 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295247 p = 1 := by simpa only [d295252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34610 p hg
    simpa only [d295252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295251 p = 1 := by simpa only [d295252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34614 p hg
    simpa only [d295252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34616 (p : Pattern) (guard : d295253 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295251 p = 1 := by simpa only [d295253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34614 p hg
    simpa only [d295253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33870 p hg
    simpa only [d295253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34617 (p : Pattern) (guard : d295254 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295252 p = 1 := by simpa only [d295254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34615 p hg
    simpa only [d295254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295253 p = 1 := by simpa only [d295254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34616 p hg
    simpa only [d295254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34618 (p : Pattern) (guard : d295255 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295254 p = 1 := by simpa only [d295255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34617 p hg
    simpa only [d295255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33870 p hg
    simpa only [d295255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34619 (p : Pattern) (guard : d295256 p = 1) : d49914 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295255 p = 1 := by simpa only [d295256, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34618 p hg
    simpa only [d295256, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295256, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33874 p hg
    simpa only [d295256, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34620 (p : Pattern) (guard : d295257 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295257, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33826 p hg
    simpa only [d295257, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295256 p = 1 := by simpa only [d295257, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34619 p hg
    simpa only [d295257, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34621 (p : Pattern) (guard : d295258 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295253 p = 1 := by simpa only [d295258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34616 p hg
    simpa only [d295258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33870 p hg
    simpa only [d295258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34622 (p : Pattern) (guard : d295259 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295258 p = 1 := by simpa only [d295259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34621 p hg
    simpa only [d295259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33870 p hg
    simpa only [d295259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34623 (p : Pattern) (guard : d295260 p = 1) : d49914 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295259 p = 1 := by simpa only [d295260, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34622 p hg
    simpa only [d295260, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295260, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33874 p hg
    simpa only [d295260, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34624 (p : Pattern) (guard : d295261 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295261, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33826 p hg
    simpa only [d295261, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295260 p = 1 := by simpa only [d295261, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34623 p hg
    simpa only [d295261, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34625 (p : Pattern) (guard : d295262 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295257 p = 1 := by simpa only [d295262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34620 p hg
    simpa only [d295262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295261 p = 1 := by simpa only [d295262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34624 p hg
    simpa only [d295262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34626 (p : Pattern) (guard : d295263 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295262 p = 1 := by simpa only [d295263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34625 p hg
    simpa only [d295263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34627 (p : Pattern) (guard : d295264 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295263 p = 1 := by simpa only [d295264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34626 p hg
    simpa only [d295264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34628 (p : Pattern) (guard : d295265 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295264 p = 1 := by simpa only [d295265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34627 p hg
    simpa only [d295265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34629 (p : Pattern) (guard : d295266 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295261 p = 1 := by simpa only [d295266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34624 p hg
    simpa only [d295266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34630 (p : Pattern) (guard : d295267 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295266 p = 1 := by simpa only [d295267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34629 p hg
    simpa only [d295267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34631 (p : Pattern) (guard : d295268 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295267 p = 1 := by simpa only [d295268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34630 p hg
    simpa only [d295268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34632 (p : Pattern) (guard : d295269 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295268 p = 1 := by simpa only [d295269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34631 p hg
    simpa only [d295269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34633 (p : Pattern) (guard : d295270 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295265 p = 1 := by simpa only [d295270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34628 p hg
    simpa only [d295270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295269 p = 1 := by simpa only [d295270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34632 p hg
    simpa only [d295270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34634 (p : Pattern) (guard : d295271 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295270 p = 1 := by simpa only [d295271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34633 p hg
    simpa only [d295271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34635 (p : Pattern) (guard : d295272 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295271 p = 1 := by simpa only [d295272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34634 p hg
    simpa only [d295272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34636 (p : Pattern) (guard : d295273 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295272 p = 1 := by simpa only [d295273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34635 p hg
    simpa only [d295273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34637 (p : Pattern) (guard : d295274 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295273 p = 1 := by simpa only [d295274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34636 p hg
    simpa only [d295274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34638 (p : Pattern) (guard : d295275 p = 1) : d49916 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295275, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295275, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295274 p = 1 := by simpa only [d295275, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34637 p hg
    simpa only [d295275, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34639 (p : Pattern) (guard : d295247 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295247, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33896 p hg
    simpa only [d295247, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295246 p = 1 := by simpa only [d295247, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34609 p hg
    simpa only [d295247, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34640 (p : Pattern) (guard : d295251 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295251, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33896 p hg
    simpa only [d295251, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295250 p = 1 := by simpa only [d295251, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d295251, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34641 (p : Pattern) (guard : d295252 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295247 p = 1 := by simpa only [d295252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34639 p hg
    simpa only [d295252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295251 p = 1 := by simpa only [d295252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34640 p hg
    simpa only [d295252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34642 (p : Pattern) (guard : d295253 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295251 p = 1 := by simpa only [d295253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34640 p hg
    simpa only [d295253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33900 p hg
    simpa only [d295253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34643 (p : Pattern) (guard : d295254 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295252 p = 1 := by simpa only [d295254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34641 p hg
    simpa only [d295254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295253 p = 1 := by simpa only [d295254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34642 p hg
    simpa only [d295254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34644 (p : Pattern) (guard : d295255 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295254 p = 1 := by simpa only [d295255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34643 p hg
    simpa only [d295255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33900 p hg
    simpa only [d295255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34645 (p : Pattern) (guard : d295256 p = 1) : d49894 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295255 p = 1 := by simpa only [d295256, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34644 p hg
    simpa only [d295256, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295256, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33874 p hg
    simpa only [d295256, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34646 (p : Pattern) (guard : d295257 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295257, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33895 p hg
    simpa only [d295257, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295256 p = 1 := by simpa only [d295257, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34645 p hg
    simpa only [d295257, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34647 (p : Pattern) (guard : d295258 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295253 p = 1 := by simpa only [d295258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34642 p hg
    simpa only [d295258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33900 p hg
    simpa only [d295258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34648 (p : Pattern) (guard : d295259 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295258 p = 1 := by simpa only [d295259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34647 p hg
    simpa only [d295259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33900 p hg
    simpa only [d295259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34649 (p : Pattern) (guard : d295260 p = 1) : d49894 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295259 p = 1 := by simpa only [d295260, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34648 p hg
    simpa only [d295260, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295260, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33874 p hg
    simpa only [d295260, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34650 (p : Pattern) (guard : d295261 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295261, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33895 p hg
    simpa only [d295261, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295260 p = 1 := by simpa only [d295261, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34649 p hg
    simpa only [d295261, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34651 (p : Pattern) (guard : d295262 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295257 p = 1 := by simpa only [d295262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34646 p hg
    simpa only [d295262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295261 p = 1 := by simpa only [d295262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34650 p hg
    simpa only [d295262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34652 (p : Pattern) (guard : d295263 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295262 p = 1 := by simpa only [d295263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34651 p hg
    simpa only [d295263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34653 (p : Pattern) (guard : d295264 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295263 p = 1 := by simpa only [d295264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34652 p hg
    simpa only [d295264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34654 (p : Pattern) (guard : d295265 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295264 p = 1 := by simpa only [d295265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34653 p hg
    simpa only [d295265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34655 (p : Pattern) (guard : d295266 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295261 p = 1 := by simpa only [d295266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34650 p hg
    simpa only [d295266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34656 (p : Pattern) (guard : d295267 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295266 p = 1 := by simpa only [d295267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34655 p hg
    simpa only [d295267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34657 (p : Pattern) (guard : d295268 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295267 p = 1 := by simpa only [d295268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34656 p hg
    simpa only [d295268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34658 (p : Pattern) (guard : d295269 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295268 p = 1 := by simpa only [d295269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34657 p hg
    simpa only [d295269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34659 (p : Pattern) (guard : d295270 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295265 p = 1 := by simpa only [d295270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34654 p hg
    simpa only [d295270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295269 p = 1 := by simpa only [d295270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34658 p hg
    simpa only [d295270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34660 (p : Pattern) (guard : d295271 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295270 p = 1 := by simpa only [d295271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34659 p hg
    simpa only [d295271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34661 (p : Pattern) (guard : d295272 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295271 p = 1 := by simpa only [d295272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34660 p hg
    simpa only [d295272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34662 (p : Pattern) (guard : d295273 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295272 p = 1 := by simpa only [d295273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34661 p hg
    simpa only [d295273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34663 (p : Pattern) (guard : d295274 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295273 p = 1 := by simpa only [d295274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34662 p hg
    simpa only [d295274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34664 (p : Pattern) (guard : d295278 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295264 p = 1 := by simpa only [d295278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34627 p hg
    simpa only [d295278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34665 (p : Pattern) (guard : d295279 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295268 p = 1 := by simpa only [d295279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34631 p hg
    simpa only [d295279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34666 (p : Pattern) (guard : d295280 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295278 p = 1 := by simpa only [d295280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34664 p hg
    simpa only [d295280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295279 p = 1 := by simpa only [d295280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34665 p hg
    simpa only [d295280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34667 (p : Pattern) (guard : d295281 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295280 p = 1 := by simpa only [d295281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34666 p hg
    simpa only [d295281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34668 (p : Pattern) (guard : d295282 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295281 p = 1 := by simpa only [d295282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34667 p hg
    simpa only [d295282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34669 (p : Pattern) (guard : d295283 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295282 p = 1 := by simpa only [d295283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34668 p hg
    simpa only [d295283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34670 (p : Pattern) (guard : d295284 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295283 p = 1 := by simpa only [d295284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34669 p hg
    simpa only [d295284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34671 (p : Pattern) (guard : d295285 p = 1) : d49916 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d295274 p = 1 := by simpa only [d295285, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34663 p hg
    simpa only [d295285, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295284 p = 1 := by simpa only [d295285, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34670 p hg
    simpa only [d295285, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34672 (p : Pattern) (guard : d295286 p = 1) : d49916 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d295275 p = 1 := by simpa only [d295286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34638 p hg
    simpa only [d295286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295285 p = 1 := by simpa only [d295286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34671 p hg
    simpa only [d295286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34673 (p : Pattern) (guard : d295287 p = 1) : d49916 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d295286 p = 1 := by simpa only [d295287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34672 p hg
    simpa only [d295287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33823 p hg
    simpa only [d295287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34674 (p : Pattern) (guard : d295763 p = 1) : d49916 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d295287 p = 1 := by simpa only [d295763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34673 p hg
    simpa only [d295763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33823 p hg
    simpa only [d295763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34675 (p : Pattern) (guard : d295764 p = 1) : d49916 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33823 p hg
    simpa only [d295764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295763 p = 1 := by simpa only [d295764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34674 p hg
    simpa only [d295764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34676 (p : Pattern) (guard : d2014 p = 1) : d47706 p ≤ (0 : Int) + d47706 p := by
  omega
theorem compare34677 (p : Pattern) (guard : d32701 p = 1) : d49927 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2014 p = 1 := by simpa only [d32701, d49927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34676 p hg
    simpa only [d32701, d49927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32701, d49927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33944 p hg
    simpa only [d32701, d49927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34678 (p : Pattern) (guard : d32702 p = 1) : d49927 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d32701 p = 1 := by simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34677 p hg
    simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33942 p hg
    simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34679 (p : Pattern) (guard : d32703 p = 1) : d49927 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d32702 p = 1 := by simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34678 p hg
    simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33942 p hg
    simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34680 (p : Pattern) (guard : d294185 p = 1) : d49927 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33942 p hg
    simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32703 p = 1 := by simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34679 p hg
    simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34681 (p : Pattern) (guard : d294186 p = 1) : d49927 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d294185 p = 1 := by simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34680 p hg
    simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33942 p hg
    simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34682 (p : Pattern) (guard : d294187 p = 1) : d49929 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294186 p = 1 := by simpa only [d294187, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34681 p hg
    simpa only [d294187, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294187, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33950 p hg
    simpa only [d294187, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34683 (p : Pattern) (guard : d294188 p = 1) : d49929 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294187 p = 1 := by simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34682 p hg
    simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33952 p hg
    simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34684 (p : Pattern) (guard : d294189 p = 1) : d49957 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294188 p = 1 := by simpa only [d294189, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34683 p hg
    simpa only [d294189, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294189, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33954 p hg
    simpa only [d294189, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34685 (p : Pattern) (guard : d294190 p = 1) : d49958 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294189 p = 1 := by simpa only [d294190, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34684 p hg
    simpa only [d294190, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294190, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d294190, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34686 (p : Pattern) (guard : d294191 p = 1) : d49978 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294191, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33941 p hg
    simpa only [d294191, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294190 p = 1 := by simpa only [d294191, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34685 p hg
    simpa only [d294191, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34687 (p : Pattern) (guard : d294192 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294191 p = 1 := by simpa only [d294192, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34686 p hg
    simpa only [d294192, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294192, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33958 p hg
    simpa only [d294192, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34688 (p : Pattern) (guard : d295242 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33940 p hg
    simpa only [d295242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294192 p = 1 := by simpa only [d295242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34687 p hg
    simpa only [d295242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34689 (p : Pattern) (guard : d295243 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33940 p hg
    simpa only [d295243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295242 p = 1 := by simpa only [d295243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34688 p hg
    simpa only [d295243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34690 (p : Pattern) (guard : d294204 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d294192 p = 1 := by simpa only [d294204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34687 p hg
    simpa only [d294204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33940 p hg
    simpa only [d294204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34691 (p : Pattern) (guard : d295244 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d295242 p = 1 := by simpa only [d295244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34688 p hg
    simpa only [d295244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294204 p = 1 := by simpa only [d295244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34690 p hg
    simpa only [d295244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34692 (p : Pattern) (guard : d295245 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295243 p = 1 := by simpa only [d295245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34689 p hg
    simpa only [d295245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295244 p = 1 := by simpa only [d295245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34691 p hg
    simpa only [d295245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34693 (p : Pattern) (guard : d295246 p = 1) : d49983 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295246, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33939 p hg
    simpa only [d295246, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295245 p = 1 := by simpa only [d295246, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34692 p hg
    simpa only [d295246, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34694 (p : Pattern) (guard : d295247 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295247, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33938 p hg
    simpa only [d295247, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295246 p = 1 := by simpa only [d295247, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34693 p hg
    simpa only [d295247, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34695 (p : Pattern) (guard : d295248 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294204 p = 1 := by simpa only [d295248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34690 p hg
    simpa only [d295248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33940 p hg
    simpa only [d295248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34696 (p : Pattern) (guard : d295249 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295244 p = 1 := by simpa only [d295249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34691 p hg
    simpa only [d295249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295248 p = 1 := by simpa only [d295249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34695 p hg
    simpa only [d295249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34697 (p : Pattern) (guard : d295250 p = 1) : d49983 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295250, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33939 p hg
    simpa only [d295250, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295249 p = 1 := by simpa only [d295250, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34696 p hg
    simpa only [d295250, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34698 (p : Pattern) (guard : d295251 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295251, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33938 p hg
    simpa only [d295251, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295250 p = 1 := by simpa only [d295251, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34697 p hg
    simpa only [d295251, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34699 (p : Pattern) (guard : d295252 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295247 p = 1 := by simpa only [d295252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34694 p hg
    simpa only [d295252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295251 p = 1 := by simpa only [d295252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34698 p hg
    simpa only [d295252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34700 (p : Pattern) (guard : d295253 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295251 p = 1 := by simpa only [d295253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34698 p hg
    simpa only [d295253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33980 p hg
    simpa only [d295253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34701 (p : Pattern) (guard : d295254 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295252 p = 1 := by simpa only [d295254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34699 p hg
    simpa only [d295254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295253 p = 1 := by simpa only [d295254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34700 p hg
    simpa only [d295254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34702 (p : Pattern) (guard : d295255 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295254 p = 1 := by simpa only [d295255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34701 p hg
    simpa only [d295255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33980 p hg
    simpa only [d295255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34703 (p : Pattern) (guard : d295256 p = 1) : d49999 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295255 p = 1 := by simpa only [d295256, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34702 p hg
    simpa only [d295256, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295256, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33984 p hg
    simpa only [d295256, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34704 (p : Pattern) (guard : d295257 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295257, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33937 p hg
    simpa only [d295257, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295256 p = 1 := by simpa only [d295257, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34703 p hg
    simpa only [d295257, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34705 (p : Pattern) (guard : d295258 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295253 p = 1 := by simpa only [d295258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34700 p hg
    simpa only [d295258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33980 p hg
    simpa only [d295258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34706 (p : Pattern) (guard : d295259 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295258 p = 1 := by simpa only [d295259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34705 p hg
    simpa only [d295259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33980 p hg
    simpa only [d295259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34707 (p : Pattern) (guard : d295260 p = 1) : d49999 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295259 p = 1 := by simpa only [d295260, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34706 p hg
    simpa only [d295260, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295260, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33984 p hg
    simpa only [d295260, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34708 (p : Pattern) (guard : d295261 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295261, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33937 p hg
    simpa only [d295261, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295260 p = 1 := by simpa only [d295261, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34707 p hg
    simpa only [d295261, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34709 (p : Pattern) (guard : d295262 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295257 p = 1 := by simpa only [d295262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34704 p hg
    simpa only [d295262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295261 p = 1 := by simpa only [d295262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34708 p hg
    simpa only [d295262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34710 (p : Pattern) (guard : d295263 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295262 p = 1 := by simpa only [d295263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34709 p hg
    simpa only [d295263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d295263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34711 (p : Pattern) (guard : d295264 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295263 p = 1 := by simpa only [d295264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34710 p hg
    simpa only [d295264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d295264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34712 (p : Pattern) (guard : d295278 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295264 p = 1 := by simpa only [d295278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34711 p hg
    simpa only [d295278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d295278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34713 (p : Pattern) (guard : d295266 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295261 p = 1 := by simpa only [d295266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34708 p hg
    simpa only [d295266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d295266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34714 (p : Pattern) (guard : d295267 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295266 p = 1 := by simpa only [d295267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34713 p hg
    simpa only [d295267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d295267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34715 (p : Pattern) (guard : d295268 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295267 p = 1 := by simpa only [d295268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34714 p hg
    simpa only [d295268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d295268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34716 (p : Pattern) (guard : d295279 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295268 p = 1 := by simpa only [d295279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34715 p hg
    simpa only [d295279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d295279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34717 (p : Pattern) (guard : d295280 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295278 p = 1 := by simpa only [d295280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34712 p hg
    simpa only [d295280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295279 p = 1 := by simpa only [d295280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34716 p hg
    simpa only [d295280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34718 (p : Pattern) (guard : d295281 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d295281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295280 p = 1 := by simpa only [d295281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34717 p hg
    simpa only [d295281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34719 (p : Pattern) (guard : d295282 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295281 p = 1 := by simpa only [d295282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34718 p hg
    simpa only [d295282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d295282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34720 (p : Pattern) (guard : d295283 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d295283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295282 p = 1 := by simpa only [d295283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34719 p hg
    simpa only [d295283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34721 (p : Pattern) (guard : d295284 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d295284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295283 p = 1 := by simpa only [d295284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34720 p hg
    simpa only [d295284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34722 (p : Pattern) (guard : d295765 p = 1) : d50001 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295765, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295765, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295284 p = 1 := by simpa only [d295765, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34721 p hg
    simpa only [d295765, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34723 (p : Pattern) (guard : d295766 p = 1) : d50001 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33935 p hg
    simpa only [d295766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295765 p = 1 := by simpa only [d295766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34722 p hg
    simpa only [d295766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34724 (p : Pattern) (guard : d295767 p = 1) : d50001 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d295766 p = 1 := by simpa only [d295767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34723 p hg
    simpa only [d295767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33935 p hg
    simpa only [d295767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34725 (p : Pattern) (guard : d295768 p = 1) : d50001 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d295767 p = 1 := by simpa only [d295768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34724 p hg
    simpa only [d295768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33935 p hg
    simpa only [d295768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34726 (p : Pattern) (guard : d295769 p = 1) : d50001 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d295768 p = 1 := by simpa only [d295769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34725 p hg
    simpa only [d295769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33935 p hg
    simpa only [d295769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34727 (p : Pattern) (guard : d295770 p = 1) : d50002 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d295764 p = 1 := by simpa only [d295770, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34675 p hg
    simpa only [d295770, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295769 p = 1 := by simpa only [d295770, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34726 p hg
    simpa only [d295770, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34728 (p : Pattern) (guard : d2014 p = 1) : d47630 p ≤ (0 : Int) + d47630 p := by
  omega
theorem compare34729 (p : Pattern) (guard : d32701 p = 1) : d49808 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2014 p = 1 := by simpa only [d32701, d49808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34728 p hg
    simpa only [d32701, d49808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32701, d49808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34018 p hg
    simpa only [d32701, d49808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34730 (p : Pattern) (guard : d32702 p = 1) : d49808 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d32701 p = 1 := by simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34729 p hg
    simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34016 p hg
    simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34731 (p : Pattern) (guard : d32703 p = 1) : d49808 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d32702 p = 1 := by simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34730 p hg
    simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34016 p hg
    simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34732 (p : Pattern) (guard : d294185 p = 1) : d49808 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34016 p hg
    simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32703 p = 1 := by simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34731 p hg
    simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34733 (p : Pattern) (guard : d294186 p = 1) : d49808 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d294185 p = 1 := by simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34732 p hg
    simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34016 p hg
    simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34734 (p : Pattern) (guard : d294187 p = 1) : d49831 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294186 p = 1 := by simpa only [d294187, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34733 p hg
    simpa only [d294187, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294187, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34024 p hg
    simpa only [d294187, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34735 (p : Pattern) (guard : d294188 p = 1) : d49831 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294187 p = 1 := by simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34015 p hg
    simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34736 (p : Pattern) (guard : d294360 p = 1) : d49831 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34015 p hg
    simpa only [d294360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294188 p = 1 := by simpa only [d294360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34735 p hg
    simpa only [d294360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34737 (p : Pattern) (guard : d294189 p = 1) : d50030 p ≤ (0 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294188 p = 1 := by simpa only [d294189, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34599 p hg
    simpa only [d294189, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294189, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33954 p hg
    simpa only [d294189, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34738 (p : Pattern) (guard : d294361 p = 1) : d50031 p ≤ (0 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294360 p = 1 := by simpa only [d294361, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d294361, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294189 p = 1 := by simpa only [d294361, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34737 p hg
    simpa only [d294361, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34739 (p : Pattern) (guard : d2014 p = 1) : d47634 p ≤ (0 : Int) + d47634 p := by
  omega
theorem compare34740 (p : Pattern) (guard : d32701 p = 1) : d49811 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2014 p = 1 := by simpa only [d32701, d49811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34739 p hg
    simpa only [d32701, d49811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32701, d49811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34032 p hg
    simpa only [d32701, d49811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34741 (p : Pattern) (guard : d32702 p = 1) : d49811 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d32701 p = 1 := by simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34740 p hg
    simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34030 p hg
    simpa only [d32702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34742 (p : Pattern) (guard : d32703 p = 1) : d49811 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d32702 p = 1 := by simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34741 p hg
    simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34030 p hg
    simpa only [d32703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34743 (p : Pattern) (guard : d294185 p = 1) : d49811 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34030 p hg
    simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32703 p = 1 := by simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34742 p hg
    simpa only [d294185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34744 (p : Pattern) (guard : d294186 p = 1) : d49811 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d294185 p = 1 := by simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34743 p hg
    simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34030 p hg
    simpa only [d294186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34745 (p : Pattern) (guard : d294187 p = 1) : d49857 p ≤ (0 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294186 p = 1 := by simpa only [d294187, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34744 p hg
    simpa only [d294187, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294187, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34038 p hg
    simpa only [d294187, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34746 (p : Pattern) (guard : d294188 p = 1) : d49857 p ≤ (0 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294187 p = 1 := by simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34745 p hg
    simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34040 p hg
    simpa only [d294188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34747 (p : Pattern) (guard : d294189 p = 1) : d49865 p ≤ (0 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294188 p = 1 := by simpa only [d294189, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34746 p hg
    simpa only [d294189, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294189, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d294189, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34748 (p : Pattern) (guard : d294190 p = 1) : d49866 p ≤ (0 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294189 p = 1 := by simpa only [d294190, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34747 p hg
    simpa only [d294190, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294190, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d294190, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34749 (p : Pattern) (guard : d294362 p = 1) : d50032 p ≤ (0 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d294361 p = 1 := by simpa only [d294362, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34738 p hg
    simpa only [d294362, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294190 p = 1 := by simpa only [d294362, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34748 p hg
    simpa only [d294362, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
