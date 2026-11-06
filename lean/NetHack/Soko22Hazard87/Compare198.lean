import NetHack.Soko22Hazard87.Compare197
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare49500 (p : Pattern) (guard : d46885 p = 1) : d50576 p ≤ (0 : Int) + d371064 p := by
  cases selected : p 157 with
  | false =>
    have hg : d46882 p = 1 := by simpa only [d46885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49497 p hg
    simpa only [d46885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46884 p = 1 := by simpa only [d46885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49499 p hg
    simpa only [d46885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49501 (p : Pattern) (guard : d46886 p = 1) : d50577 p ≤ (0 : Int) + d371065 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46886, d50577, d371065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49464 p hg
    simpa only [d46886, d50577, d371065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46885 p = 1 := by simpa only [d46886, d50577, d371065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49500 p hg
    simpa only [d46886, d50577, d371065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49502 (p : Pattern) (guard : d46887 p = 1) : d50578 p ≤ (0 : Int) + d371066 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46887, d50578, d371066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49463 p hg
    simpa only [d46887, d50578, d371066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46886 p = 1 := by simpa only [d46887, d50578, d371066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49501 p hg
    simpa only [d46887, d50578, d371066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49503 (p : Pattern) (guard : d46888 p = 1) : d50553 p ≤ (0 : Int) + d371040 p := by
  cases selected : p 180 with
  | false =>
    have hg : d46875 p = 1 := by simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49487 p hg
    simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49467 p hg
    simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49504 (p : Pattern) (guard : d46889 p = 1) : d50570 p ≤ (0 : Int) + d371058 p := by
  cases selected : p 163 with
  | false =>
    have hg : d46888 p = 1 := by simpa only [d46889, d50570, d371058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49503 p hg
    simpa only [d46889, d50570, d371058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46889, d50570, d371058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49489 p hg
    simpa only [d46889, d50570, d371058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49505 (p : Pattern) (guard : d46890 p = 1) : d50571 p ≤ (0 : Int) + d371059 p := by
  cases selected : p 162 with
  | false =>
    have hg : d46889 p = 1 := by simpa only [d46890, d50571, d371059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49504 p hg
    simpa only [d46890, d50571, d371059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46890, d50571, d371059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49491 p hg
    simpa only [d46890, d50571, d371059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49506 (p : Pattern) (guard : d46891 p = 1) : d50572 p ≤ (0 : Int) + d371060 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46891, d50572, d371060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49466 p hg
    simpa only [d46891, d50572, d371060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46890 p = 1 := by simpa only [d46891, d50572, d371060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49505 p hg
    simpa only [d46891, d50572, d371060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49507 (p : Pattern) (guard : d46892 p = 1) : d50576 p ≤ (0 : Int) + d371064 p := by
  cases selected : p 160 with
  | false =>
    have hg : d46891 p = 1 := by simpa only [d46892, d50576, d371064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49506 p hg
    simpa only [d46892, d50576, d371064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46892, d50576, d371064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49494 p hg
    simpa only [d46892, d50576, d371064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49508 (p : Pattern) (guard : d46893 p = 1) : d50576 p ≤ (0 : Int) + d371064 p := by
  cases selected : p 159 with
  | false =>
    have hg : d46892 p = 1 := by simpa only [d46893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49507 p hg
    simpa only [d46893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49465 p hg
    simpa only [d46893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49509 (p : Pattern) (guard : d46894 p = 1) : d50576 p ≤ (0 : Int) + d371064 p := by
  cases selected : p 158 with
  | false =>
    have hg : d46883 p = 1 := by simpa only [d46894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49498 p hg
    simpa only [d46894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46893 p = 1 := by simpa only [d46894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49508 p hg
    simpa only [d46894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49510 (p : Pattern) (guard : d46895 p = 1) : d50576 p ≤ (0 : Int) + d371064 p := by
  cases selected : p 157 with
  | false =>
    have hg : d46884 p = 1 := by simpa only [d46895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49499 p hg
    simpa only [d46895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46894 p = 1 := by simpa only [d46895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49509 p hg
    simpa only [d46895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49511 (p : Pattern) (guard : d46896 p = 1) : d50577 p ≤ (0 : Int) + d371065 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46896, d50577, d371065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49464 p hg
    simpa only [d46896, d50577, d371065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46895 p = 1 := by simpa only [d46896, d50577, d371065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49510 p hg
    simpa only [d46896, d50577, d371065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49512 (p : Pattern) (guard : d46897 p = 1) : d50578 p ≤ (0 : Int) + d371066 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46897, d50578, d371066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49463 p hg
    simpa only [d46897, d50578, d371066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46896 p = 1 := by simpa only [d46897, d50578, d371066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49511 p hg
    simpa only [d46897, d50578, d371066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49513 (p : Pattern) (guard : d46898 p = 1) : d50578 p ≤ (0 : Int) + d371066 p := by
  cases selected : p 136 with
  | false =>
    have hg : d46887 p = 1 := by simpa only [d46898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49502 p hg
    simpa only [d46898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46897 p = 1 := by simpa only [d46898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49512 p hg
    simpa only [d46898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49514 (p : Pattern) (guard : d0 p = 1) : d50578 p ≤ (0 : Int) + d371066 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49515 (p : Pattern) (guard : d46899 p = 1) : d50578 p ≤ (0 : Int) + d371066 p := by
  cases selected : p 136 with
  | false =>
    have hg : d46897 p = 1 := by simpa only [d46899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49512 p hg
    simpa only [d46899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49514 p hg
    simpa only [d46899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49516 (p : Pattern) (guard : d46900 p = 1) : d50578 p ≤ (0 : Int) + d371066 p := by
  cases selected : p 135 with
  | false =>
    have hg : d46898 p = 1 := by simpa only [d46900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49513 p hg
    simpa only [d46900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46899 p = 1 := by simpa only [d46900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49515 p hg
    simpa only [d46900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49517 (p : Pattern) (guard : d46901 p = 1) : d50578 p ≤ (0 : Int) + d371066 p := by
  cases selected : p 119 with
  | false =>
    have hg : d46900 p = 1 := by simpa only [d46901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49516 p hg
    simpa only [d46901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49514 p hg
    simpa only [d46901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49518 (p : Pattern) (guard : d0 p = 1) : d50589 p ≤ (0 : Int) + d371077 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49519 (p : Pattern) (guard : d46902 p = 1) : d50590 p ≤ (0 : Int) + d371078 p := by
  cases selected : p 116 with
  | false =>
    have hg : d46901 p = 1 := by simpa only [d46902, d50590, d371078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49517 p hg
    simpa only [d46902, d50590, d371078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46902, d50590, d371078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49518 p hg
    simpa only [d46902, d50590, d371078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49520 (p : Pattern) (guard : d46903 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46903, d50591, d371079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49462 p hg
    simpa only [d46903, d50591, d371079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46902 p = 1 := by simpa only [d46903, d50591, d371079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49519 p hg
    simpa only [d46903, d50591, d371079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49521 (p : Pattern) (guard : d46904 p = 1) : d50578 p ≤ (0 : Int) + d371066 p := by
  cases selected : p 135 with
  | false =>
    have hg : d46899 p = 1 := by simpa only [d46904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49515 p hg
    simpa only [d46904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49514 p hg
    simpa only [d46904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49522 (p : Pattern) (guard : d46905 p = 1) : d50578 p ≤ (0 : Int) + d371066 p := by
  cases selected : p 119 with
  | false =>
    have hg : d46904 p = 1 := by simpa only [d46905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49521 p hg
    simpa only [d46905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49514 p hg
    simpa only [d46905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49523 (p : Pattern) (guard : d46906 p = 1) : d50590 p ≤ (0 : Int) + d371078 p := by
  cases selected : p 116 with
  | false =>
    have hg : d46905 p = 1 := by simpa only [d46906, d50590, d371078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49522 p hg
    simpa only [d46906, d50590, d371078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46906, d50590, d371078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49518 p hg
    simpa only [d46906, d50590, d371078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49524 (p : Pattern) (guard : d46907 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46907, d50591, d371079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49462 p hg
    simpa only [d46907, d50591, d371079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46906 p = 1 := by simpa only [d46907, d50591, d371079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49523 p hg
    simpa only [d46907, d50591, d371079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49525 (p : Pattern) (guard : d46908 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 113 with
  | false =>
    have hg : d46903 p = 1 := by simpa only [d46908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49520 p hg
    simpa only [d46908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46907 p = 1 := by simpa only [d46908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49524 p hg
    simpa only [d46908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49526 (p : Pattern) (guard : d46909 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 96 with
  | false =>
    have hg : d46908 p = 1 := by simpa only [d46909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49525 p hg
    simpa only [d46909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d46909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49527 (p : Pattern) (guard : d46910 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 95 with
  | false =>
    have hg : d46909 p = 1 := by simpa only [d46910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49526 p hg
    simpa only [d46910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d46910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49528 (p : Pattern) (guard : d46911 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d46911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46910 p = 1 := by simpa only [d46911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49527 p hg
    simpa only [d46911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49529 (p : Pattern) (guard : d46912 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 113 with
  | false =>
    have hg : d46907 p = 1 := by simpa only [d46912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49524 p hg
    simpa only [d46912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d46912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49530 (p : Pattern) (guard : d46913 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 96 with
  | false =>
    have hg : d46912 p = 1 := by simpa only [d46913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49529 p hg
    simpa only [d46913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d46913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49531 (p : Pattern) (guard : d46914 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 95 with
  | false =>
    have hg : d46913 p = 1 := by simpa only [d46914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49530 p hg
    simpa only [d46914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d46914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49532 (p : Pattern) (guard : d46915 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d46915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46914 p = 1 := by simpa only [d46915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49531 p hg
    simpa only [d46915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49533 (p : Pattern) (guard : d46916 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 91 with
  | false =>
    have hg : d46911 p = 1 := by simpa only [d46916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49528 p hg
    simpa only [d46916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46915 p = 1 := by simpa only [d46916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49532 p hg
    simpa only [d46916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49534 (p : Pattern) (guard : d46917 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d46917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46916 p = 1 := by simpa only [d46917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49533 p hg
    simpa only [d46917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49535 (p : Pattern) (guard : d46918 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 89 with
  | false =>
    have hg : d46917 p = 1 := by simpa only [d46918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49534 p hg
    simpa only [d46918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d46918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49536 (p : Pattern) (guard : d46919 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d46919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46918 p = 1 := by simpa only [d46919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49535 p hg
    simpa only [d46919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49537 (p : Pattern) (guard : d46920 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d46920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46919 p = 1 := by simpa only [d46920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49536 p hg
    simpa only [d46920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49538 (p : Pattern) (guard : d46921 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d46921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46920 p = 1 := by simpa only [d46921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49537 p hg
    simpa only [d46921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49539 (p : Pattern) (guard : d46924 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 93 with
  | false =>
    have hg : d46910 p = 1 := by simpa only [d46924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49527 p hg
    simpa only [d46924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d46924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49540 (p : Pattern) (guard : d46925 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 93 with
  | false =>
    have hg : d46914 p = 1 := by simpa only [d46925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49531 p hg
    simpa only [d46925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d46925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49541 (p : Pattern) (guard : d46926 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 91 with
  | false =>
    have hg : d46924 p = 1 := by simpa only [d46926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49539 p hg
    simpa only [d46926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46925 p = 1 := by simpa only [d46926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49540 p hg
    simpa only [d46926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49542 (p : Pattern) (guard : d46927 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d46927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46926 p = 1 := by simpa only [d46927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49541 p hg
    simpa only [d46927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49543 (p : Pattern) (guard : d46928 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 89 with
  | false =>
    have hg : d46927 p = 1 := by simpa only [d46928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49542 p hg
    simpa only [d46928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d46928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49544 (p : Pattern) (guard : d46929 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d46929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46928 p = 1 := by simpa only [d46929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49543 p hg
    simpa only [d46929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49545 (p : Pattern) (guard : d46930 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d46930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46929 p = 1 := by simpa only [d46930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49544 p hg
    simpa only [d46930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49546 (p : Pattern) (guard : d46931 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 71 with
  | false =>
    have hg : d46920 p = 1 := by simpa only [d46931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49537 p hg
    simpa only [d46931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46930 p = 1 := by simpa only [d46931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49545 p hg
    simpa only [d46931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49547 (p : Pattern) (guard : d46932 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 70 with
  | false =>
    have hg : d46921 p = 1 := by simpa only [d46932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49538 p hg
    simpa only [d46932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46931 p = 1 := by simpa only [d46932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49546 p hg
    simpa only [d46932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49548 (p : Pattern) (guard : d46933 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 69 with
  | false =>
    have hg : d46932 p = 1 := by simpa only [d46933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49547 p hg
    simpa only [d46933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d46933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49549 (p : Pattern) (guard : d321908 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 51 with
  | false =>
    have hg : d46933 p = 1 := by simpa only [d321908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49548 p hg
    simpa only [d321908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d321908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d321908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49550 (p : Pattern) (guard : d321909 p = 1) : d50591 p ≤ (0 : Int) + d371079 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d321909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321908 p = 1 := by simpa only [d321909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49549 p hg
    simpa only [d321909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49551 (p : Pattern) (guard : d0 p = 1) : d50675 p ≤ (0 : Int) + d371190 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49552 (p : Pattern) (guard : d0 p = 1) : d50674 p ≤ (0 : Int) + d371189 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49553 (p : Pattern) (guard : d0 p = 1) : d50671 p ≤ (0 : Int) + d371186 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49554 (p : Pattern) (guard : d0 p = 1) : d50631 p ≤ (0 : Int) + d371145 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49555 (p : Pattern) (guard : d0 p = 1) : d50653 p ≤ (0 : Int) + d371168 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49556 (p : Pattern) (guard : d0 p = 1) : d50663 p ≤ (0 : Int) + d371178 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49557 (p : Pattern) (guard : d0 p = 1) : d50656 p ≤ (0 : Int) + d371171 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49558 (p : Pattern) (guard : d0 p = 1) : d50642 p ≤ (0 : Int) + d371157 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49559 (p : Pattern) (guard : d0 p = 1) : d47706 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49560 (p : Pattern) (guard : d0 p = 1) : d49565 p ≤ (0 : Int) + d371114 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49561 (p : Pattern) (guard : d44880 p = 1) : d5 p ≤ (0 : Int) + d5 p := by
  omega
theorem compare49562 (p : Pattern) (guard : d0 p = 1) : d47705 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49563 (p : Pattern) (guard : d46864 p = 1) : d47706 p ≤ (0 : Int) + d5 p := by
  cases selected : p 246 with
  | false =>
    have hg : d44880 p = 1 := by simpa only [d46864, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49561 p hg
    simpa only [d46864, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46864, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49562 p hg
    simpa only [d46864, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49564 (p : Pattern) (guard : d46865 p = 1) : d47706 p ≤ (0 : Int) + d5 p := by
  cases selected : p 226 with
  | false =>
    have hg : d46864 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49563 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49559 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49565 (p : Pattern) (guard : d0 p = 1) : d49560 p ≤ (0 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49566 (p : Pattern) (guard : d46866 p = 1) : d49561 p ≤ (0 : Int) + d371113 p := by
  cases selected : p 225 with
  | false =>
    have hg : d46865 p = 1 := by simpa only [d46866, d49561, d371113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49564 p hg
    simpa only [d46866, d49561, d371113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46866, d49561, d371113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49565 p hg
    simpa only [d46866, d49561, d371113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49567 (p : Pattern) (guard : d0 p = 1) : d49564 p ≤ (0 : Int) + d370953 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49568 (p : Pattern) (guard : d46867 p = 1) : d49565 p ≤ (0 : Int) + d371114 p := by
  cases selected : p 224 with
  | false =>
    have hg : d46866 p = 1 := by simpa only [d46867, d49565, d371114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49566 p hg
    simpa only [d46867, d49565, d371114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46867, d49565, d371114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49567 p hg
    simpa only [d46867, d49565, d371114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49569 (p : Pattern) (guard : d46868 p = 1) : d49565 p ≤ (0 : Int) + d371114 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49560 p hg
    simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46867 p = 1 := by simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49568 p hg
    simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49570 (p : Pattern) (guard : d46869 p = 1) : d50606 p ≤ (0 : Int) + d371115 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46869, d50606, d371115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49559 p hg
    simpa only [d46869, d50606, d371115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46868 p = 1 := by simpa only [d46869, d50606, d371115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49569 p hg
    simpa only [d46869, d50606, d371115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49571 (p : Pattern) (guard : d0 p = 1) : d50606 p ≤ (0 : Int) + d371115 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49572 (p : Pattern) (guard : d46870 p = 1) : d50606 p ≤ (0 : Int) + d371115 p := by
  cases selected : p 202 with
  | false =>
    have hg : d46869 p = 1 := by simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49570 p hg
    simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49571 p hg
    simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49573 (p : Pattern) (guard : d46871 p = 1) : d49565 p ≤ (0 : Int) + d371114 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46867 p = 1 := by simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49568 p hg
    simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49560 p hg
    simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49574 (p : Pattern) (guard : d46872 p = 1) : d50606 p ≤ (0 : Int) + d371115 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46872, d50606, d371115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49559 p hg
    simpa only [d46872, d50606, d371115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46871 p = 1 := by simpa only [d46872, d50606, d371115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49573 p hg
    simpa only [d46872, d50606, d371115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49575 (p : Pattern) (guard : d46873 p = 1) : d50606 p ≤ (0 : Int) + d371115 p := by
  cases selected : p 202 with
  | false =>
    have hg : d46872 p = 1 := by simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49574 p hg
    simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49571 p hg
    simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49576 (p : Pattern) (guard : d46874 p = 1) : d50606 p ≤ (0 : Int) + d371115 p := by
  cases selected : p 201 with
  | false =>
    have hg : d46870 p = 1 := by simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49572 p hg
    simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46873 p = 1 := by simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49575 p hg
    simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49577 (p : Pattern) (guard : d0 p = 1) : d49566 p ≤ (0 : Int) + d371156 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49578 (p : Pattern) (guard : d46875 p = 1) : d50642 p ≤ (0 : Int) + d371157 p := by
  cases selected : p 182 with
  | false =>
    have hg : d46874 p = 1 := by simpa only [d46875, d50642, d371157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49576 p hg
    simpa only [d46875, d50642, d371157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46875, d50642, d371157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49577 p hg
    simpa only [d46875, d50642, d371157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49579 (p : Pattern) (guard : d46876 p = 1) : d50642 p ≤ (0 : Int) + d371157 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49558 p hg
    simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46875 p = 1 := by simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49578 p hg
    simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49580 (p : Pattern) (guard : d0 p = 1) : d50530 p ≤ (0 : Int) + d371012 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49581 (p : Pattern) (guard : d46877 p = 1) : d50657 p ≤ (0 : Int) + d371172 p := by
  cases selected : p 163 with
  | false =>
    have hg : d46876 p = 1 := by simpa only [d46877, d50657, d371172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49579 p hg
    simpa only [d46877, d50657, d371172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46877, d50657, d371172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49580 p hg
    simpa only [d46877, d50657, d371172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49582 (p : Pattern) (guard : d46878 p = 1) : d50658 p ≤ (0 : Int) + d371173 p := by
  cases selected : p 162 with
  | false =>
    have hg : d46877 p = 1 := by simpa only [d46878, d50658, d371173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49581 p hg
    simpa only [d46878, d50658, d371173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46878, d50658, d371173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d46878, d50658, d371173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49583 (p : Pattern) (guard : d46879 p = 1) : d50659 p ≤ (0 : Int) + d371174 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46879, d50659, d371174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49557 p hg
    simpa only [d46879, d50659, d371174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46878 p = 1 := by simpa only [d46879, d50659, d371174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49582 p hg
    simpa only [d46879, d50659, d371174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49584 (p : Pattern) (guard : d0 p = 1) : d50662 p ≤ (0 : Int) + d371177 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49585 (p : Pattern) (guard : d46880 p = 1) : d50663 p ≤ (0 : Int) + d371178 p := by
  cases selected : p 160 with
  | false =>
    have hg : d46879 p = 1 := by simpa only [d46880, d50663, d371178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49583 p hg
    simpa only [d46880, d50663, d371178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46880, d50663, d371178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49584 p hg
    simpa only [d46880, d50663, d371178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49586 (p : Pattern) (guard : d46881 p = 1) : d50663 p ≤ (0 : Int) + d371178 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49556 p hg
    simpa only [d46881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46880 p = 1 := by simpa only [d46881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49585 p hg
    simpa only [d46881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49587 (p : Pattern) (guard : d46882 p = 1) : d50663 p ≤ (0 : Int) + d371178 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49556 p hg
    simpa only [d46882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46881 p = 1 := by simpa only [d46882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49586 p hg
    simpa only [d46882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49588 (p : Pattern) (guard : d46883 p = 1) : d50663 p ≤ (0 : Int) + d371178 p := by
  cases selected : p 159 with
  | false =>
    have hg : d46880 p = 1 := by simpa only [d46883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49585 p hg
    simpa only [d46883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49556 p hg
    simpa only [d46883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49589 (p : Pattern) (guard : d46884 p = 1) : d50663 p ≤ (0 : Int) + d371178 p := by
  cases selected : p 158 with
  | false =>
    have hg : d46881 p = 1 := by simpa only [d46884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49586 p hg
    simpa only [d46884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46883 p = 1 := by simpa only [d46884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49588 p hg
    simpa only [d46884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49590 (p : Pattern) (guard : d46885 p = 1) : d50663 p ≤ (0 : Int) + d371178 p := by
  cases selected : p 157 with
  | false =>
    have hg : d46882 p = 1 := by simpa only [d46885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49587 p hg
    simpa only [d46885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46884 p = 1 := by simpa only [d46885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49589 p hg
    simpa only [d46885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49591 (p : Pattern) (guard : d46886 p = 1) : d50664 p ≤ (0 : Int) + d371179 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46886, d50664, d371179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49555 p hg
    simpa only [d46886, d50664, d371179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46885 p = 1 := by simpa only [d46886, d50664, d371179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49590 p hg
    simpa only [d46886, d50664, d371179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49592 (p : Pattern) (guard : d46887 p = 1) : d50665 p ≤ (0 : Int) + d371180 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46887, d50665, d371180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49554 p hg
    simpa only [d46887, d50665, d371180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46886 p = 1 := by simpa only [d46887, d50665, d371180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49591 p hg
    simpa only [d46887, d50665, d371180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49593 (p : Pattern) (guard : d46888 p = 1) : d50642 p ≤ (0 : Int) + d371157 p := by
  cases selected : p 180 with
  | false =>
    have hg : d46875 p = 1 := by simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49578 p hg
    simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49558 p hg
    simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49594 (p : Pattern) (guard : d46889 p = 1) : d50657 p ≤ (0 : Int) + d371172 p := by
  cases selected : p 163 with
  | false =>
    have hg : d46888 p = 1 := by simpa only [d46889, d50657, d371172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49593 p hg
    simpa only [d46889, d50657, d371172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46889, d50657, d371172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49580 p hg
    simpa only [d46889, d50657, d371172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49595 (p : Pattern) (guard : d46890 p = 1) : d50658 p ≤ (0 : Int) + d371173 p := by
  cases selected : p 162 with
  | false =>
    have hg : d46889 p = 1 := by simpa only [d46890, d50658, d371173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49594 p hg
    simpa only [d46890, d50658, d371173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46890, d50658, d371173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d46890, d50658, d371173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49596 (p : Pattern) (guard : d46891 p = 1) : d50659 p ≤ (0 : Int) + d371174 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46891, d50659, d371174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49557 p hg
    simpa only [d46891, d50659, d371174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46890 p = 1 := by simpa only [d46891, d50659, d371174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49595 p hg
    simpa only [d46891, d50659, d371174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49597 (p : Pattern) (guard : d46892 p = 1) : d50663 p ≤ (0 : Int) + d371178 p := by
  cases selected : p 160 with
  | false =>
    have hg : d46891 p = 1 := by simpa only [d46892, d50663, d371178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49596 p hg
    simpa only [d46892, d50663, d371178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46892, d50663, d371178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49584 p hg
    simpa only [d46892, d50663, d371178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49598 (p : Pattern) (guard : d46893 p = 1) : d50663 p ≤ (0 : Int) + d371178 p := by
  cases selected : p 159 with
  | false =>
    have hg : d46892 p = 1 := by simpa only [d46893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49597 p hg
    simpa only [d46893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49556 p hg
    simpa only [d46893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49599 (p : Pattern) (guard : d46894 p = 1) : d50663 p ≤ (0 : Int) + d371178 p := by
  cases selected : p 158 with
  | false =>
    have hg : d46883 p = 1 := by simpa only [d46894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49588 p hg
    simpa only [d46894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46893 p = 1 := by simpa only [d46894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49598 p hg
    simpa only [d46894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49600 (p : Pattern) (guard : d46895 p = 1) : d50663 p ≤ (0 : Int) + d371178 p := by
  cases selected : p 157 with
  | false =>
    have hg : d46884 p = 1 := by simpa only [d46895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49589 p hg
    simpa only [d46895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46894 p = 1 := by simpa only [d46895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49599 p hg
    simpa only [d46895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49601 (p : Pattern) (guard : d46896 p = 1) : d50664 p ≤ (0 : Int) + d371179 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46896, d50664, d371179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49555 p hg
    simpa only [d46896, d50664, d371179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46895 p = 1 := by simpa only [d46896, d50664, d371179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49600 p hg
    simpa only [d46896, d50664, d371179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49602 (p : Pattern) (guard : d46897 p = 1) : d50665 p ≤ (0 : Int) + d371180 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46897, d50665, d371180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49554 p hg
    simpa only [d46897, d50665, d371180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46896 p = 1 := by simpa only [d46897, d50665, d371180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49601 p hg
    simpa only [d46897, d50665, d371180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49603 (p : Pattern) (guard : d46898 p = 1) : d50665 p ≤ (0 : Int) + d371180 p := by
  cases selected : p 136 with
  | false =>
    have hg : d46887 p = 1 := by simpa only [d46898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49592 p hg
    simpa only [d46898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46897 p = 1 := by simpa only [d46898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49602 p hg
    simpa only [d46898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49604 (p : Pattern) (guard : d0 p = 1) : d50665 p ≤ (0 : Int) + d371180 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49605 (p : Pattern) (guard : d46899 p = 1) : d50665 p ≤ (0 : Int) + d371180 p := by
  cases selected : p 136 with
  | false =>
    have hg : d46897 p = 1 := by simpa only [d46899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49602 p hg
    simpa only [d46899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49604 p hg
    simpa only [d46899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49606 (p : Pattern) (guard : d46900 p = 1) : d50665 p ≤ (0 : Int) + d371180 p := by
  cases selected : p 135 with
  | false =>
    have hg : d46898 p = 1 := by simpa only [d46900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49603 p hg
    simpa only [d46900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46899 p = 1 := by simpa only [d46900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49605 p hg
    simpa only [d46900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49607 (p : Pattern) (guard : d46901 p = 1) : d50665 p ≤ (0 : Int) + d371180 p := by
  cases selected : p 119 with
  | false =>
    have hg : d46900 p = 1 := by simpa only [d46901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49606 p hg
    simpa only [d46901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49604 p hg
    simpa only [d46901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49608 (p : Pattern) (guard : d0 p = 1) : d50672 p ≤ (0 : Int) + d371187 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49609 (p : Pattern) (guard : d46902 p = 1) : d50673 p ≤ (0 : Int) + d371188 p := by
  cases selected : p 116 with
  | false =>
    have hg : d46901 p = 1 := by simpa only [d46902, d50673, d371188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49607 p hg
    simpa only [d46902, d50673, d371188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46902, d50673, d371188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49608 p hg
    simpa only [d46902, d50673, d371188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49610 (p : Pattern) (guard : d46903 p = 1) : d50674 p ≤ (0 : Int) + d371189 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46903, d50674, d371189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49553 p hg
    simpa only [d46903, d50674, d371189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46902 p = 1 := by simpa only [d46903, d50674, d371189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49609 p hg
    simpa only [d46903, d50674, d371189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49611 (p : Pattern) (guard : d46904 p = 1) : d50665 p ≤ (0 : Int) + d371180 p := by
  cases selected : p 135 with
  | false =>
    have hg : d46899 p = 1 := by simpa only [d46904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49605 p hg
    simpa only [d46904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49604 p hg
    simpa only [d46904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49612 (p : Pattern) (guard : d46905 p = 1) : d50665 p ≤ (0 : Int) + d371180 p := by
  cases selected : p 119 with
  | false =>
    have hg : d46904 p = 1 := by simpa only [d46905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49611 p hg
    simpa only [d46905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49604 p hg
    simpa only [d46905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49613 (p : Pattern) (guard : d46906 p = 1) : d50673 p ≤ (0 : Int) + d371188 p := by
  cases selected : p 116 with
  | false =>
    have hg : d46905 p = 1 := by simpa only [d46906, d50673, d371188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49612 p hg
    simpa only [d46906, d50673, d371188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46906, d50673, d371188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49608 p hg
    simpa only [d46906, d50673, d371188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49614 (p : Pattern) (guard : d46907 p = 1) : d50674 p ≤ (0 : Int) + d371189 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46907, d50674, d371189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49553 p hg
    simpa only [d46907, d50674, d371189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46906 p = 1 := by simpa only [d46907, d50674, d371189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49613 p hg
    simpa only [d46907, d50674, d371189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49615 (p : Pattern) (guard : d46908 p = 1) : d50674 p ≤ (0 : Int) + d371189 p := by
  cases selected : p 113 with
  | false =>
    have hg : d46903 p = 1 := by simpa only [d46908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49610 p hg
    simpa only [d46908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46907 p = 1 := by simpa only [d46908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49614 p hg
    simpa only [d46908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49616 (p : Pattern) (guard : d46909 p = 1) : d50674 p ≤ (0 : Int) + d371189 p := by
  cases selected : p 96 with
  | false =>
    have hg : d46908 p = 1 := by simpa only [d46909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49615 p hg
    simpa only [d46909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49552 p hg
    simpa only [d46909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49617 (p : Pattern) (guard : d46910 p = 1) : d50674 p ≤ (0 : Int) + d371189 p := by
  cases selected : p 95 with
  | false =>
    have hg : d46909 p = 1 := by simpa only [d46910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49616 p hg
    simpa only [d46910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49552 p hg
    simpa only [d46910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49618 (p : Pattern) (guard : d46924 p = 1) : d50674 p ≤ (0 : Int) + d371189 p := by
  cases selected : p 93 with
  | false =>
    have hg : d46910 p = 1 := by simpa only [d46924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49617 p hg
    simpa only [d46924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49552 p hg
    simpa only [d46924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49619 (p : Pattern) (guard : d46912 p = 1) : d50674 p ≤ (0 : Int) + d371189 p := by
  cases selected : p 113 with
  | false =>
    have hg : d46907 p = 1 := by simpa only [d46912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49614 p hg
    simpa only [d46912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49552 p hg
    simpa only [d46912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49620 (p : Pattern) (guard : d46913 p = 1) : d50674 p ≤ (0 : Int) + d371189 p := by
  cases selected : p 96 with
  | false =>
    have hg : d46912 p = 1 := by simpa only [d46913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49619 p hg
    simpa only [d46913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49552 p hg
    simpa only [d46913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49621 (p : Pattern) (guard : d46914 p = 1) : d50674 p ≤ (0 : Int) + d371189 p := by
  cases selected : p 95 with
  | false =>
    have hg : d46913 p = 1 := by simpa only [d46914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49620 p hg
    simpa only [d46914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49552 p hg
    simpa only [d46914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49622 (p : Pattern) (guard : d46925 p = 1) : d50674 p ≤ (0 : Int) + d371189 p := by
  cases selected : p 93 with
  | false =>
    have hg : d46914 p = 1 := by simpa only [d46925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49621 p hg
    simpa only [d46925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49552 p hg
    simpa only [d46925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49623 (p : Pattern) (guard : d46926 p = 1) : d50674 p ≤ (0 : Int) + d371189 p := by
  cases selected : p 91 with
  | false =>
    have hg : d46924 p = 1 := by simpa only [d46926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49618 p hg
    simpa only [d46926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46925 p = 1 := by simpa only [d46926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49622 p hg
    simpa only [d46926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49624 (p : Pattern) (guard : d46927 p = 1) : d50674 p ≤ (0 : Int) + d371189 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49552 p hg
    simpa only [d46927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46926 p = 1 := by simpa only [d46927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49623 p hg
    simpa only [d46927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49625 (p : Pattern) (guard : d46928 p = 1) : d50674 p ≤ (0 : Int) + d371189 p := by
  cases selected : p 89 with
  | false =>
    have hg : d46927 p = 1 := by simpa only [d46928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49624 p hg
    simpa only [d46928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49552 p hg
    simpa only [d46928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49626 (p : Pattern) (guard : d46929 p = 1) : d50674 p ≤ (0 : Int) + d371189 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49552 p hg
    simpa only [d46929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46928 p = 1 := by simpa only [d46929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49625 p hg
    simpa only [d46929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49627 (p : Pattern) (guard : d46930 p = 1) : d50674 p ≤ (0 : Int) + d371189 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49552 p hg
    simpa only [d46930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46929 p = 1 := by simpa only [d46930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49626 p hg
    simpa only [d46930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49628 (p : Pattern) (guard : d321910 p = 1) : d50675 p ≤ (0 : Int) + d371190 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321910, d50675, d371190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d321910, d50675, d371190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46930 p = 1 := by simpa only [d321910, d50675, d371190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49627 p hg
    simpa only [d321910, d50675, d371190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49629 (p : Pattern) (guard : d321911 p = 1) : d50675 p ≤ (0 : Int) + d371190 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49551 p hg
    simpa only [d321911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321910 p = 1 := by simpa only [d321911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49628 p hg
    simpa only [d321911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49630 (p : Pattern) (guard : d321912 p = 1) : d50675 p ≤ (0 : Int) + d371190 p := by
  cases selected : p 69 with
  | false =>
    have hg : d321911 p = 1 := by simpa only [d321912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49629 p hg
    simpa only [d321912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d321912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49551 p hg
    simpa only [d321912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49631 (p : Pattern) (guard : d321913 p = 1) : d50675 p ≤ (0 : Int) + d371190 p := by
  cases selected : p 51 with
  | false =>
    have hg : d321912 p = 1 := by simpa only [d321913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49630 p hg
    simpa only [d321913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d321913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49551 p hg
    simpa only [d321913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49632 (p : Pattern) (guard : d321914 p = 1) : d50675 p ≤ (0 : Int) + d371190 p := by
  cases selected : p 50 with
  | false =>
    have hg : d321913 p = 1 := by simpa only [d321914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49631 p hg
    simpa only [d321914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d321914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49551 p hg
    simpa only [d321914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49633 (p : Pattern) (guard : d321915 p = 1) : d50676 p ≤ (0 : Int) + d371191 p := by
  cases selected : p 49 with
  | false =>
    have hg : d321909 p = 1 := by simpa only [d321915, d50676, d371191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49550 p hg
    simpa only [d321915, d50676, d371191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d321914 p = 1 := by simpa only [d321915, d50676, d371191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49632 p hg
    simpa only [d321915, d50676, d371191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49634 (p : Pattern) (guard : d0 p = 1) : d50739 p ≤ (0 : Int) + d371261 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49635 (p : Pattern) (guard : d0 p = 1) : d50738 p ≤ (0 : Int) + d371260 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49636 (p : Pattern) (guard : d0 p = 1) : d50712 p ≤ (0 : Int) + d371229 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49637 (p : Pattern) (guard : d0 p = 1) : d50724 p ≤ (0 : Int) + d371243 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49638 (p : Pattern) (guard : d0 p = 1) : d50733 p ≤ (0 : Int) + d371255 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49639 (p : Pattern) (guard : d0 p = 1) : d50725 p ≤ (0 : Int) + d371247 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49640 (p : Pattern) (guard : d0 p = 1) : d50560 p ≤ (0 : Int) + d371048 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49641 (p : Pattern) (guard : d0 p = 1) : d47630 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49642 (p : Pattern) (guard : d0 p = 1) : d49316 p ≤ (0 : Int) + d370969 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49643 (p : Pattern) (guard : d44880 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare49644 (p : Pattern) (guard : d0 p = 1) : d47629 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49645 (p : Pattern) (guard : d46864 p = 1) : d47630 p ≤ (0 : Int) + d2 p := by
  cases selected : p 246 with
  | false =>
    have hg : d44880 p = 1 := by simpa only [d46864, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49643 p hg
    simpa only [d46864, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46864, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49644 p hg
    simpa only [d46864, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49646 (p : Pattern) (guard : d46865 p = 1) : d47630 p ≤ (0 : Int) + d2 p := by
  cases selected : p 226 with
  | false =>
    have hg : d46864 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49645 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49641 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49647 (p : Pattern) (guard : d0 p = 1) : d49310 p ≤ (0 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49648 (p : Pattern) (guard : d46866 p = 1) : d49311 p ≤ (0 : Int) + d370967 p := by
  cases selected : p 225 with
  | false =>
    have hg : d46865 p = 1 := by simpa only [d46866, d49311, d370967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49646 p hg
    simpa only [d46866, d49311, d370967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46866, d49311, d370967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49647 p hg
    simpa only [d46866, d49311, d370967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49649 (p : Pattern) (guard : d0 p = 1) : d49315 p ≤ (0 : Int) + d370968 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49650 (p : Pattern) (guard : d46867 p = 1) : d49316 p ≤ (0 : Int) + d370969 p := by
  cases selected : p 224 with
  | false =>
    have hg : d46866 p = 1 := by simpa only [d46867, d49316, d370969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49648 p hg
    simpa only [d46867, d49316, d370969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46867, d49316, d370969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49649 p hg
    simpa only [d46867, d49316, d370969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49651 (p : Pattern) (guard : d46868 p = 1) : d49316 p ≤ (0 : Int) + d370969 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49642 p hg
    simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46867 p = 1 := by simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49650 p hg
    simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49652 (p : Pattern) (guard : d46869 p = 1) : d50534 p ≤ (0 : Int) + d371016 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46869, d50534, d371016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49641 p hg
    simpa only [d46869, d50534, d371016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46868 p = 1 := by simpa only [d46869, d50534, d371016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49651 p hg
    simpa only [d46869, d50534, d371016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49653 (p : Pattern) (guard : d0 p = 1) : d50534 p ≤ (0 : Int) + d371016 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49654 (p : Pattern) (guard : d46870 p = 1) : d50534 p ≤ (0 : Int) + d371016 p := by
  cases selected : p 202 with
  | false =>
    have hg : d46869 p = 1 := by simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49652 p hg
    simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49653 p hg
    simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49655 (p : Pattern) (guard : d46871 p = 1) : d49316 p ≤ (0 : Int) + d370969 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46867 p = 1 := by simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49650 p hg
    simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49642 p hg
    simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49656 (p : Pattern) (guard : d46872 p = 1) : d50534 p ≤ (0 : Int) + d371016 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46872, d50534, d371016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49641 p hg
    simpa only [d46872, d50534, d371016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46871 p = 1 := by simpa only [d46872, d50534, d371016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49655 p hg
    simpa only [d46872, d50534, d371016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49657 (p : Pattern) (guard : d46873 p = 1) : d50534 p ≤ (0 : Int) + d371016 p := by
  cases selected : p 202 with
  | false =>
    have hg : d46872 p = 1 := by simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49656 p hg
    simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49653 p hg
    simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49658 (p : Pattern) (guard : d46874 p = 1) : d50534 p ≤ (0 : Int) + d371016 p := by
  cases selected : p 201 with
  | false =>
    have hg : d46870 p = 1 := by simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49654 p hg
    simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46873 p = 1 := by simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49657 p hg
    simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49659 (p : Pattern) (guard : d0 p = 1) : d49317 p ≤ (0 : Int) + d370970 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49660 (p : Pattern) (guard : d46875 p = 1) : d50560 p ≤ (0 : Int) + d371048 p := by
  cases selected : p 182 with
  | false =>
    have hg : d46874 p = 1 := by simpa only [d46875, d50560, d371048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49658 p hg
    simpa only [d46875, d50560, d371048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46875, d50560, d371048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49659 p hg
    simpa only [d46875, d50560, d371048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49661 (p : Pattern) (guard : d46876 p = 1) : d50560 p ≤ (0 : Int) + d371048 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49640 p hg
    simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46875 p = 1 := by simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49660 p hg
    simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49662 (p : Pattern) (guard : d47086 p = 1) : d50726 p ≤ (0 : Int) + d371248 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47086, d50726, d371248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49639 p hg
    simpa only [d47086, d50726, d371248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46876 p = 1 := by simpa only [d47086, d50726, d371248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49661 p hg
    simpa only [d47086, d50726, d371248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49663 (p : Pattern) (guard : d46877 p = 1) : d50727 p ≤ (0 : Int) + d371249 p := by
  cases selected : p 163 with
  | false =>
    have hg : d46876 p = 1 := by simpa only [d46877, d50727, d371249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49488 p hg
    simpa only [d46877, d50727, d371249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46877, d50727, d371249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49580 p hg
    simpa only [d46877, d50727, d371249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49664 (p : Pattern) (guard : d47087 p = 1) : d50728 p ≤ (0 : Int) + d371250 p := by
  cases selected : p 162 with
  | false =>
    have hg : d47086 p = 1 := by simpa only [d47087, d50728, d371250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49662 p hg
    simpa only [d47087, d50728, d371250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46877 p = 1 := by simpa only [d47087, d50728, d371250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49663 p hg
    simpa only [d47087, d50728, d371250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49665 (p : Pattern) (guard : d0 p = 1) : d50562 p ≤ (0 : Int) + d371050 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49666 (p : Pattern) (guard : d0 p = 1) : d47634 p ≤ (0 : Int) + d6 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49667 (p : Pattern) (guard : d0 p = 1) : d49323 p ≤ (0 : Int) + d370974 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49668 (p : Pattern) (guard : d44880 p = 1) : d6 p ≤ (0 : Int) + d6 p := by
  omega
theorem compare49669 (p : Pattern) (guard : d0 p = 1) : d47633 p ≤ (0 : Int) + d6 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49670 (p : Pattern) (guard : d46864 p = 1) : d47634 p ≤ (0 : Int) + d6 p := by
  cases selected : p 246 with
  | false =>
    have hg : d44880 p = 1 := by simpa only [d46864, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49668 p hg
    simpa only [d46864, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46864, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49669 p hg
    simpa only [d46864, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49671 (p : Pattern) (guard : d46865 p = 1) : d47634 p ≤ (0 : Int) + d6 p := by
  cases selected : p 226 with
  | false =>
    have hg : d46864 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49670 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49666 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49672 (p : Pattern) (guard : d0 p = 1) : d47963 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49673 (p : Pattern) (guard : d46866 p = 1) : d49319 p ≤ (0 : Int) + d370972 p := by
  cases selected : p 225 with
  | false =>
    have hg : d46865 p = 1 := by simpa only [d46866, d49319, d370972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49671 p hg
    simpa only [d46866, d49319, d370972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46866, d49319, d370972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49672 p hg
    simpa only [d46866, d49319, d370972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49674 (p : Pattern) (guard : d0 p = 1) : d49322 p ≤ (0 : Int) + d370973 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49675 (p : Pattern) (guard : d46867 p = 1) : d49323 p ≤ (0 : Int) + d370974 p := by
  cases selected : p 224 with
  | false =>
    have hg : d46866 p = 1 := by simpa only [d46867, d49323, d370974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49673 p hg
    simpa only [d46867, d49323, d370974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46867, d49323, d370974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49674 p hg
    simpa only [d46867, d49323, d370974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49676 (p : Pattern) (guard : d46868 p = 1) : d49323 p ≤ (0 : Int) + d370974 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49667 p hg
    simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46867 p = 1 := by simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49675 p hg
    simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49677 (p : Pattern) (guard : d46869 p = 1) : d50561 p ≤ (0 : Int) + d371049 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46869, d50561, d371049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49666 p hg
    simpa only [d46869, d50561, d371049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46868 p = 1 := by simpa only [d46869, d50561, d371049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49676 p hg
    simpa only [d46869, d50561, d371049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49678 (p : Pattern) (guard : d0 p = 1) : d50561 p ≤ (0 : Int) + d371049 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49679 (p : Pattern) (guard : d46870 p = 1) : d50561 p ≤ (0 : Int) + d371049 p := by
  cases selected : p 202 with
  | false =>
    have hg : d46869 p = 1 := by simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49677 p hg
    simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49678 p hg
    simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49680 (p : Pattern) (guard : d46871 p = 1) : d49323 p ≤ (0 : Int) + d370974 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46867 p = 1 := by simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49675 p hg
    simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49667 p hg
    simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49681 (p : Pattern) (guard : d46872 p = 1) : d50561 p ≤ (0 : Int) + d371049 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46872, d50561, d371049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49666 p hg
    simpa only [d46872, d50561, d371049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46871 p = 1 := by simpa only [d46872, d50561, d371049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49680 p hg
    simpa only [d46872, d50561, d371049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49682 (p : Pattern) (guard : d46873 p = 1) : d50561 p ≤ (0 : Int) + d371049 p := by
  cases selected : p 202 with
  | false =>
    have hg : d46872 p = 1 := by simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49681 p hg
    simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49678 p hg
    simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49683 (p : Pattern) (guard : d46874 p = 1) : d50561 p ≤ (0 : Int) + d371049 p := by
  cases selected : p 201 with
  | false =>
    have hg : d46870 p = 1 := by simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49679 p hg
    simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46873 p = 1 := by simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49682 p hg
    simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49684 (p : Pattern) (guard : d0 p = 1) : d49324 p ≤ (0 : Int) + d370975 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49685 (p : Pattern) (guard : d46875 p = 1) : d50562 p ≤ (0 : Int) + d371050 p := by
  cases selected : p 182 with
  | false =>
    have hg : d46874 p = 1 := by simpa only [d46875, d50562, d371050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49683 p hg
    simpa only [d46875, d50562, d371050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46875, d50562, d371050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49684 p hg
    simpa only [d46875, d50562, d371050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49686 (p : Pattern) (guard : d46876 p = 1) : d50562 p ≤ (0 : Int) + d371050 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49665 p hg
    simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46875 p = 1 := by simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49685 p hg
    simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49687 (p : Pattern) (guard : d46877 p = 1) : d50573 p ≤ (0 : Int) + d371061 p := by
  cases selected : p 163 with
  | false =>
    have hg : d46876 p = 1 := by simpa only [d46877, d50573, d371061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49686 p hg
    simpa only [d46877, d50573, d371061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46877, d50573, d371061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d46877, d50573, d371061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49688 (p : Pattern) (guard : d46878 p = 1) : d50574 p ≤ (0 : Int) + d371062 p := by
  cases selected : p 162 with
  | false =>
    have hg : d46877 p = 1 := by simpa only [d46878, d50574, d371062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49687 p hg
    simpa only [d46878, d50574, d371062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46878, d50574, d371062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d46878, d50574, d371062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49689 (p : Pattern) (guard : d47088 p = 1) : d50729 p ≤ (0 : Int) + d371251 p := by
  cases selected : p 161 with
  | false =>
    have hg : d47087 p = 1 := by simpa only [d47088, d50729, d371251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49664 p hg
    simpa only [d47088, d50729, d371251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46878 p = 1 := by simpa only [d47088, d50729, d371251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49688 p hg
    simpa only [d47088, d50729, d371251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49690 (p : Pattern) (guard : d0 p = 1) : d50732 p ≤ (0 : Int) + d371254 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49691 (p : Pattern) (guard : d47089 p = 1) : d50733 p ≤ (0 : Int) + d371255 p := by
  cases selected : p 160 with
  | false =>
    have hg : d47088 p = 1 := by simpa only [d47089, d50733, d371255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49689 p hg
    simpa only [d47089, d50733, d371255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47089, d50733, d371255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49690 p hg
    simpa only [d47089, d50733, d371255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49692 (p : Pattern) (guard : d47090 p = 1) : d50733 p ≤ (0 : Int) + d371255 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49638 p hg
    simpa only [d47090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47089 p = 1 := by simpa only [d47090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49691 p hg
    simpa only [d47090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49693 (p : Pattern) (guard : d47091 p = 1) : d50733 p ≤ (0 : Int) + d371255 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49638 p hg
    simpa only [d47091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47090 p = 1 := by simpa only [d47091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49692 p hg
    simpa only [d47091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49694 (p : Pattern) (guard : d47095 p = 1) : d50733 p ≤ (0 : Int) + d371255 p := by
  cases selected : p 159 with
  | false =>
    have hg : d47089 p = 1 := by simpa only [d47095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49691 p hg
    simpa only [d47095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49638 p hg
    simpa only [d47095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49695 (p : Pattern) (guard : d47096 p = 1) : d50733 p ≤ (0 : Int) + d371255 p := by
  cases selected : p 158 with
  | false =>
    have hg : d47090 p = 1 := by simpa only [d47096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49692 p hg
    simpa only [d47096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47095 p = 1 := by simpa only [d47096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49694 p hg
    simpa only [d47096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49696 (p : Pattern) (guard : d47097 p = 1) : d50733 p ≤ (0 : Int) + d371255 p := by
  cases selected : p 157 with
  | false =>
    have hg : d47091 p = 1 := by simpa only [d47097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49693 p hg
    simpa only [d47097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47096 p = 1 := by simpa only [d47097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49695 p hg
    simpa only [d47097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49697 (p : Pattern) (guard : d47098 p = 1) : d50734 p ≤ (0 : Int) + d371256 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47098, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49637 p hg
    simpa only [d47098, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47097 p = 1 := by simpa only [d47098, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49696 p hg
    simpa only [d47098, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49698 (p : Pattern) (guard : d47099 p = 1) : d50735 p ≤ (0 : Int) + d371257 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47099, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49636 p hg
    simpa only [d47099, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47098 p = 1 := by simpa only [d47099, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49697 p hg
    simpa only [d47099, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49699 (p : Pattern) (guard : d46888 p = 1) : d50560 p ≤ (0 : Int) + d371048 p := by
  cases selected : p 180 with
  | false =>
    have hg : d46875 p = 1 := by simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49660 p hg
    simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49640 p hg
    simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49700 (p : Pattern) (guard : d47101 p = 1) : d50726 p ≤ (0 : Int) + d371248 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47101, d50726, d371248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49639 p hg
    simpa only [d47101, d50726, d371248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46888 p = 1 := by simpa only [d47101, d50726, d371248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49699 p hg
    simpa only [d47101, d50726, d371248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49701 (p : Pattern) (guard : d46889 p = 1) : d50727 p ≤ (0 : Int) + d371249 p := by
  cases selected : p 163 with
  | false =>
    have hg : d46888 p = 1 := by simpa only [d46889, d50727, d371249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49503 p hg
    simpa only [d46889, d50727, d371249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46889, d50727, d371249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49580 p hg
    simpa only [d46889, d50727, d371249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49702 (p : Pattern) (guard : d47102 p = 1) : d50728 p ≤ (0 : Int) + d371250 p := by
  cases selected : p 162 with
  | false =>
    have hg : d47101 p = 1 := by simpa only [d47102, d50728, d371250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49700 p hg
    simpa only [d47102, d50728, d371250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46889 p = 1 := by simpa only [d47102, d50728, d371250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49701 p hg
    simpa only [d47102, d50728, d371250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49703 (p : Pattern) (guard : d46888 p = 1) : d50562 p ≤ (0 : Int) + d371050 p := by
  cases selected : p 180 with
  | false =>
    have hg : d46875 p = 1 := by simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49685 p hg
    simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49665 p hg
    simpa only [d46888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49704 (p : Pattern) (guard : d46889 p = 1) : d50573 p ≤ (0 : Int) + d371061 p := by
  cases selected : p 163 with
  | false =>
    have hg : d46888 p = 1 := by simpa only [d46889, d50573, d371061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49703 p hg
    simpa only [d46889, d50573, d371061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46889, d50573, d371061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d46889, d50573, d371061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49705 (p : Pattern) (guard : d46890 p = 1) : d50574 p ≤ (0 : Int) + d371062 p := by
  cases selected : p 162 with
  | false =>
    have hg : d46889 p = 1 := by simpa only [d46890, d50574, d371062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49704 p hg
    simpa only [d46890, d50574, d371062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46890, d50574, d371062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d46890, d50574, d371062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49706 (p : Pattern) (guard : d47103 p = 1) : d50729 p ≤ (0 : Int) + d371251 p := by
  cases selected : p 161 with
  | false =>
    have hg : d47102 p = 1 := by simpa only [d47103, d50729, d371251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49702 p hg
    simpa only [d47103, d50729, d371251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46890 p = 1 := by simpa only [d47103, d50729, d371251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49705 p hg
    simpa only [d47103, d50729, d371251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49707 (p : Pattern) (guard : d47104 p = 1) : d50733 p ≤ (0 : Int) + d371255 p := by
  cases selected : p 160 with
  | false =>
    have hg : d47103 p = 1 := by simpa only [d47104, d50733, d371255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49706 p hg
    simpa only [d47104, d50733, d371255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47104, d50733, d371255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49690 p hg
    simpa only [d47104, d50733, d371255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49708 (p : Pattern) (guard : d47105 p = 1) : d50733 p ≤ (0 : Int) + d371255 p := by
  cases selected : p 159 with
  | false =>
    have hg : d47104 p = 1 := by simpa only [d47105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49707 p hg
    simpa only [d47105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49638 p hg
    simpa only [d47105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49709 (p : Pattern) (guard : d47106 p = 1) : d50733 p ≤ (0 : Int) + d371255 p := by
  cases selected : p 158 with
  | false =>
    have hg : d47095 p = 1 := by simpa only [d47106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49694 p hg
    simpa only [d47106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47105 p = 1 := by simpa only [d47106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49708 p hg
    simpa only [d47106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49710 (p : Pattern) (guard : d47107 p = 1) : d50733 p ≤ (0 : Int) + d371255 p := by
  cases selected : p 157 with
  | false =>
    have hg : d47096 p = 1 := by simpa only [d47107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49695 p hg
    simpa only [d47107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47106 p = 1 := by simpa only [d47107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49709 p hg
    simpa only [d47107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49711 (p : Pattern) (guard : d47108 p = 1) : d50734 p ≤ (0 : Int) + d371256 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47108, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49637 p hg
    simpa only [d47108, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47107 p = 1 := by simpa only [d47108, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49710 p hg
    simpa only [d47108, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49712 (p : Pattern) (guard : d47109 p = 1) : d50735 p ≤ (0 : Int) + d371257 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47109, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49636 p hg
    simpa only [d47109, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47108 p = 1 := by simpa only [d47109, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49711 p hg
    simpa only [d47109, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49713 (p : Pattern) (guard : d47110 p = 1) : d50735 p ≤ (0 : Int) + d371257 p := by
  cases selected : p 136 with
  | false =>
    have hg : d47099 p = 1 := by simpa only [d47110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49698 p hg
    simpa only [d47110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47109 p = 1 := by simpa only [d47110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49712 p hg
    simpa only [d47110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49714 (p : Pattern) (guard : d0 p = 1) : d50735 p ≤ (0 : Int) + d371257 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49715 (p : Pattern) (guard : d47115 p = 1) : d50735 p ≤ (0 : Int) + d371257 p := by
  cases selected : p 136 with
  | false =>
    have hg : d47109 p = 1 := by simpa only [d47115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49712 p hg
    simpa only [d47115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49714 p hg
    simpa only [d47115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49716 (p : Pattern) (guard : d47116 p = 1) : d50735 p ≤ (0 : Int) + d371257 p := by
  cases selected : p 135 with
  | false =>
    have hg : d47110 p = 1 := by simpa only [d47116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49713 p hg
    simpa only [d47116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47115 p = 1 := by simpa only [d47116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49715 p hg
    simpa only [d47116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49717 (p : Pattern) (guard : d47117 p = 1) : d50735 p ≤ (0 : Int) + d371257 p := by
  cases selected : p 119 with
  | false =>
    have hg : d47116 p = 1 := by simpa only [d47117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49716 p hg
    simpa only [d47117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49714 p hg
    simpa only [d47117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49718 (p : Pattern) (guard : d0 p = 1) : d50736 p ≤ (0 : Int) + d371258 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49719 (p : Pattern) (guard : d47118 p = 1) : d50737 p ≤ (0 : Int) + d371259 p := by
  cases selected : p 116 with
  | false =>
    have hg : d47117 p = 1 := by simpa only [d47118, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49717 p hg
    simpa only [d47118, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47118, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49718 p hg
    simpa only [d47118, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49720 (p : Pattern) (guard : d47119 p = 1) : d50738 p ≤ (0 : Int) + d371260 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47119, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49462 p hg
    simpa only [d47119, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47118 p = 1 := by simpa only [d47119, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49719 p hg
    simpa only [d47119, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49721 (p : Pattern) (guard : d47124 p = 1) : d50735 p ≤ (0 : Int) + d371257 p := by
  cases selected : p 135 with
  | false =>
    have hg : d47115 p = 1 := by simpa only [d47124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49715 p hg
    simpa only [d47124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49714 p hg
    simpa only [d47124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49722 (p : Pattern) (guard : d47125 p = 1) : d50735 p ≤ (0 : Int) + d371257 p := by
  cases selected : p 119 with
  | false =>
    have hg : d47124 p = 1 := by simpa only [d47125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49721 p hg
    simpa only [d47125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49714 p hg
    simpa only [d47125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49723 (p : Pattern) (guard : d47126 p = 1) : d50737 p ≤ (0 : Int) + d371259 p := by
  cases selected : p 116 with
  | false =>
    have hg : d47125 p = 1 := by simpa only [d47126, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49722 p hg
    simpa only [d47126, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47126, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49718 p hg
    simpa only [d47126, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49724 (p : Pattern) (guard : d47127 p = 1) : d50738 p ≤ (0 : Int) + d371260 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47127, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49462 p hg
    simpa only [d47127, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47126 p = 1 := by simpa only [d47127, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49723 p hg
    simpa only [d47127, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49725 (p : Pattern) (guard : d47128 p = 1) : d50738 p ≤ (0 : Int) + d371260 p := by
  cases selected : p 113 with
  | false =>
    have hg : d47119 p = 1 := by simpa only [d47128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49720 p hg
    simpa only [d47128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47127 p = 1 := by simpa only [d47128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49724 p hg
    simpa only [d47128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49726 (p : Pattern) (guard : d47129 p = 1) : d50738 p ≤ (0 : Int) + d371260 p := by
  cases selected : p 96 with
  | false =>
    have hg : d47128 p = 1 := by simpa only [d47129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49725 p hg
    simpa only [d47129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49635 p hg
    simpa only [d47129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49727 (p : Pattern) (guard : d47130 p = 1) : d50738 p ≤ (0 : Int) + d371260 p := by
  cases selected : p 95 with
  | false =>
    have hg : d47129 p = 1 := by simpa only [d47130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49726 p hg
    simpa only [d47130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49635 p hg
    simpa only [d47130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49728 (p : Pattern) (guard : d47131 p = 1) : d50738 p ≤ (0 : Int) + d371260 p := by
  cases selected : p 93 with
  | false =>
    have hg : d47130 p = 1 := by simpa only [d47131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49727 p hg
    simpa only [d47131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d47131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49635 p hg
    simpa only [d47131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49729 (p : Pattern) (guard : d46865 p = 1) : d47963 p ≤ (0 : Int) + d12 p := by
  have ha := bounds47963 p
  have hb := bounds12 p
  omega
theorem compare49730 (p : Pattern) (guard : d324332 p = 1) : d49319 p ≤ (0 : Int) + d370972 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324332, d49319, d370972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49666 p hg
    simpa only [d324332, d49319, d370972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46865 p = 1 := by simpa only [d324332, d49319, d370972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49729 p hg
    simpa only [d324332, d49319, d370972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49731 (p : Pattern) (guard : d44880 p = 1) : d49320 p ≤ (0 : Int) + d10 p := by
  have ha := bounds49320 p
  have hb := bounds10 p
  omega
theorem compare49732 (p : Pattern) (guard : d0 p = 1) : d47656 p ≤ (0 : Int) + d10 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49733 (p : Pattern) (guard : d46864 p = 1) : d49321 p ≤ (0 : Int) + d10 p := by
  cases selected : p 246 with
  | false =>
    have hg : d44880 p = 1 := by simpa only [d46864, d49321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49731 p hg
    simpa only [d46864, d49321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46864, d49321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49732 p hg
    simpa only [d46864, d49321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49734 (p : Pattern) (guard : d0 p = 1) : d49321 p ≤ (0 : Int) + d10 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49735 (p : Pattern) (guard : d46865 p = 1) : d49321 p ≤ (0 : Int) + d10 p := by
  cases selected : p 226 with
  | false =>
    have hg : d46864 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49733 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49734 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49736 (p : Pattern) (guard : d46866 p = 1) : d49322 p ≤ (0 : Int) + d370973 p := by
  cases selected : p 225 with
  | false =>
    have hg : d46865 p = 1 := by simpa only [d46866, d49322, d370973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49735 p hg
    simpa only [d46866, d49322, d370973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46866, d49322, d370973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49672 p hg
    simpa only [d46866, d49322, d370973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49737 (p : Pattern) (guard : d324333 p = 1) : d49323 p ≤ (0 : Int) + d370974 p := by
  cases selected : p 224 with
  | false =>
    have hg : d324332 p = 1 := by simpa only [d324333, d49323, d370974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49730 p hg
    simpa only [d324333, d49323, d370974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46866 p = 1 := by simpa only [d324333, d49323, d370974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49736 p hg
    simpa only [d324333, d49323, d370974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49738 (p : Pattern) (guard : d326576 p = 1) : d49323 p ≤ (0 : Int) + d370974 p := by
  cases selected : p 223 with
  | false =>
    have hg : d324333 p = 1 := by simpa only [d326576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49737 p hg
    simpa only [d326576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46867 p = 1 := by simpa only [d326576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49675 p hg
    simpa only [d326576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49739 (p : Pattern) (guard : d326577 p = 1) : d50561 p ≤ (0 : Int) + d371049 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d326577, d50561, d371049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49666 p hg
    simpa only [d326577, d50561, d371049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326576 p = 1 := by simpa only [d326577, d50561, d371049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49738 p hg
    simpa only [d326577, d50561, d371049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49740 (p : Pattern) (guard : d326578 p = 1) : d50561 p ≤ (0 : Int) + d371049 p := by
  cases selected : p 202 with
  | false =>
    have hg : d326577 p = 1 := by simpa only [d326578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49739 p hg
    simpa only [d326578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d326578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49678 p hg
    simpa only [d326578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49741 (p : Pattern) (guard : d326579 p = 1) : d50561 p ≤ (0 : Int) + d371049 p := by
  cases selected : p 201 with
  | false =>
    have hg : d326578 p = 1 := by simpa only [d326579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49740 p hg
    simpa only [d326579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46873 p = 1 := by simpa only [d326579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49682 p hg
    simpa only [d326579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49742 (p : Pattern) (guard : d326580 p = 1) : d50562 p ≤ (0 : Int) + d371050 p := by
  cases selected : p 182 with
  | false =>
    have hg : d326579 p = 1 := by simpa only [d326580, d50562, d371050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49741 p hg
    simpa only [d326580, d50562, d371050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d326580, d50562, d371050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49684 p hg
    simpa only [d326580, d50562, d371050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49743 (p : Pattern) (guard : d326581 p = 1) : d50562 p ≤ (0 : Int) + d371050 p := by
  cases selected : p 180 with
  | false =>
    have hg : d326580 p = 1 := by simpa only [d326581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49742 p hg
    simpa only [d326581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d326581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49665 p hg
    simpa only [d326581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49744 (p : Pattern) (guard : d326582 p = 1) : d50573 p ≤ (0 : Int) + d371061 p := by
  cases selected : p 163 with
  | false =>
    have hg : d326581 p = 1 := by simpa only [d326582, d50573, d371061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49743 p hg
    simpa only [d326582, d50573, d371061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d326582, d50573, d371061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d326582, d50573, d371061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49745 (p : Pattern) (guard : d326583 p = 1) : d50574 p ≤ (0 : Int) + d371062 p := by
  cases selected : p 162 with
  | false =>
    have hg : d326582 p = 1 := by simpa only [d326583, d50574, d371062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49744 p hg
    simpa only [d326583, d50574, d371062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d326583, d50574, d371062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d326583, d50574, d371062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49746 (p : Pattern) (guard : d326584 p = 1) : d50729 p ≤ (0 : Int) + d371251 p := by
  cases selected : p 161 with
  | false =>
    have hg : d47102 p = 1 := by simpa only [d326584, d50729, d371251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49702 p hg
    simpa only [d326584, d50729, d371251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326583 p = 1 := by simpa only [d326584, d50729, d371251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49745 p hg
    simpa only [d326584, d50729, d371251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49747 (p : Pattern) (guard : d326585 p = 1) : d50733 p ≤ (0 : Int) + d371255 p := by
  cases selected : p 160 with
  | false =>
    have hg : d326584 p = 1 := by simpa only [d326585, d50733, d371255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49746 p hg
    simpa only [d326585, d50733, d371255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d326585, d50733, d371255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49690 p hg
    simpa only [d326585, d50733, d371255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49748 (p : Pattern) (guard : d326586 p = 1) : d50733 p ≤ (0 : Int) + d371255 p := by
  cases selected : p 159 with
  | false =>
    have hg : d326585 p = 1 := by simpa only [d326586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49747 p hg
    simpa only [d326586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d326586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49638 p hg
    simpa only [d326586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49749 (p : Pattern) (guard : d326587 p = 1) : d50733 p ≤ (0 : Int) + d371255 p := by
  cases selected : p 158 with
  | false =>
    have hg : d47095 p = 1 := by simpa only [d326587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49694 p hg
    simpa only [d326587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326586 p = 1 := by simpa only [d326587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49748 p hg
    simpa only [d326587, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
