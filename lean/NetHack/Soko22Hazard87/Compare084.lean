import NetHack.Soko22Hazard87.Compare083
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare21000 (p : Pattern) (guard : d16485 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16484 p = 1 := by simpa only [d16485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20999 p hg
    simpa only [d16485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21001 (p : Pattern) (guard : d16486 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16475 p = 1 := by simpa only [d16486, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20993 p hg
    simpa only [d16486, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16485 p = 1 := by simpa only [d16486, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21000 p hg
    simpa only [d16486, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21002 (p : Pattern) (guard : d16487 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d16476 p = 1 := by simpa only [d16487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20967 p hg
    simpa only [d16487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16486 p = 1 := by simpa only [d16487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21001 p hg
    simpa only [d16487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21003 (p : Pattern) (guard : d16488 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d16487 p = 1 := by simpa only [d16488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21002 p hg
    simpa only [d16488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20387 p hg
    simpa only [d16488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21004 (p : Pattern) (guard : d171131 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 51 with
  | false =>
    have hg : d16488 p = 1 := by simpa only [d171131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21003 p hg
    simpa only [d171131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20387 p hg
    simpa only [d171131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21005 (p : Pattern) (guard : d171132 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20387 p hg
    simpa only [d171132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171131 p = 1 := by simpa only [d171132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21004 p hg
    simpa only [d171132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21006 (p : Pattern) (guard : d1099 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21007 (p : Pattern) (guard : d1100 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1099 p = 1 := by simpa only [d1100, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21006 p hg
    simpa only [d1100, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1100, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d1100, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21008 (p : Pattern) (guard : d1101 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1100 p = 1 := by simpa only [d1101, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21007 p hg
    simpa only [d1101, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1101, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d1101, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21009 (p : Pattern) (guard : d1102 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1102, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d1102, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1101 p = 1 := by simpa only [d1102, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21008 p hg
    simpa only [d1102, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21010 (p : Pattern) (guard : d1103 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1102 p = 1 := by simpa only [d1103, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21009 p hg
    simpa only [d1103, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1103, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d1103, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21011 (p : Pattern) (guard : d9788 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21012 (p : Pattern) (guard : d9789 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9788 p = 1 := by simpa only [d9789, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21011 p hg
    simpa only [d9789, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9789, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d9789, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21013 (p : Pattern) (guard : d9791 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9789 p = 1 := by simpa only [d9791, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21012 p hg
    simpa only [d9791, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9791, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d9791, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21014 (p : Pattern) (guard : d16438 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16438, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d16438, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9791 p = 1 := by simpa only [d16438, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21013 p hg
    simpa only [d16438, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21015 (p : Pattern) (guard : d16439 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16438 p = 1 := by simpa only [d16439, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21014 p hg
    simpa only [d16439, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16439, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d16439, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21016 (p : Pattern) (guard : d16440 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1103 p = 1 := by simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21010 p hg
    simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16439 p = 1 := by simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21015 p hg
    simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21017 (p : Pattern) (guard : d9777 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21018 (p : Pattern) (guard : d9778 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9777 p = 1 := by simpa only [d9778, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21017 p hg
    simpa only [d9778, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9778, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d9778, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21019 (p : Pattern) (guard : d9780 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9778 p = 1 := by simpa only [d9780, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21018 p hg
    simpa only [d9780, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9780, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d9780, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21020 (p : Pattern) (guard : d14758 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14758, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d14758, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9780 p = 1 := by simpa only [d14758, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21019 p hg
    simpa only [d14758, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21021 (p : Pattern) (guard : d14759 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14758 p = 1 := by simpa only [d14759, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21020 p hg
    simpa only [d14759, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14759, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d14759, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21022 (p : Pattern) (guard : d9799 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21023 (p : Pattern) (guard : d9800 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9799 p = 1 := by simpa only [d9800, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21022 p hg
    simpa only [d9800, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9800, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d9800, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21024 (p : Pattern) (guard : d9802 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9800 p = 1 := by simpa only [d9802, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21023 p hg
    simpa only [d9802, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9802, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d9802, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21025 (p : Pattern) (guard : d14763 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14763, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d14763, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9802 p = 1 := by simpa only [d14763, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21024 p hg
    simpa only [d14763, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21026 (p : Pattern) (guard : d14764 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14763 p = 1 := by simpa only [d14764, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21025 p hg
    simpa only [d14764, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14764, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d14764, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21027 (p : Pattern) (guard : d16441 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14759 p = 1 := by simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21021 p hg
    simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14764 p = 1 := by simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21026 p hg
    simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21028 (p : Pattern) (guard : d16442 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16440 p = 1 := by simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21016 p hg
    simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16441 p = 1 := by simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21027 p hg
    simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21029 (p : Pattern) (guard : d1109 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21030 (p : Pattern) (guard : d1110 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1109 p = 1 := by simpa only [d1110, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21029 p hg
    simpa only [d1110, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1110, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d1110, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21031 (p : Pattern) (guard : d1111 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1110 p = 1 := by simpa only [d1111, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21030 p hg
    simpa only [d1111, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1111, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d1111, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21032 (p : Pattern) (guard : d1112 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1112, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d1112, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1111 p = 1 := by simpa only [d1112, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21031 p hg
    simpa only [d1112, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21033 (p : Pattern) (guard : d1113 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1112 p = 1 := by simpa only [d1113, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21032 p hg
    simpa only [d1113, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1113, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d1113, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21034 (p : Pattern) (guard : d1120 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21035 (p : Pattern) (guard : d1121 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1120 p = 1 := by simpa only [d1121, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21034 p hg
    simpa only [d1121, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1121, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d1121, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21036 (p : Pattern) (guard : d1122 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1121 p = 1 := by simpa only [d1122, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21035 p hg
    simpa only [d1122, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d1122, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21037 (p : Pattern) (guard : d1123 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1123, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d1123, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1122 p = 1 := by simpa only [d1123, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21036 p hg
    simpa only [d1123, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21038 (p : Pattern) (guard : d1124 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1123 p = 1 := by simpa only [d1124, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21037 p hg
    simpa only [d1124, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1124, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d1124, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21039 (p : Pattern) (guard : d1125 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1113 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21033 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1124 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21038 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21040 (p : Pattern) (guard : d14765 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14764 p = 1 := by simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21026 p hg
    simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20467 p hg
    simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21041 (p : Pattern) (guard : d16443 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1125 p = 1 := by simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21039 p hg
    simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14765 p = 1 := by simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21040 p hg
    simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21042 (p : Pattern) (guard : d16444 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16442 p = 1 := by simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21028 p hg
    simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16443 p = 1 := by simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21041 p hg
    simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21043 (p : Pattern) (guard : d16445 p = 1) : d48346 p ≤ (0 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16445, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20458 p hg
    simpa only [d16445, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16444 p = 1 := by simpa only [d16445, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21042 p hg
    simpa only [d16445, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21044 (p : Pattern) (guard : d16446 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16446, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20457 p hg
    simpa only [d16446, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16445 p = 1 := by simpa only [d16446, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21043 p hg
    simpa only [d16446, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21045 (p : Pattern) (guard : d5017 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21046 (p : Pattern) (guard : d5018 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5017 p = 1 := by simpa only [d5018, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21045 p hg
    simpa only [d5018, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5018, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d5018, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21047 (p : Pattern) (guard : d5019 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5018 p = 1 := by simpa only [d5019, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21046 p hg
    simpa only [d5019, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5019, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d5019, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21048 (p : Pattern) (guard : d5020 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5020, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d5020, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5019 p = 1 := by simpa only [d5020, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21047 p hg
    simpa only [d5020, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21049 (p : Pattern) (guard : d5021 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5020 p = 1 := by simpa only [d5021, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21048 p hg
    simpa only [d5021, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5021, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d5021, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21050 (p : Pattern) (guard : d5022 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5021 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21049 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20467 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21051 (p : Pattern) (guard : d9843 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21052 (p : Pattern) (guard : d9844 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9843 p = 1 := by simpa only [d9844, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21051 p hg
    simpa only [d9844, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9844, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d9844, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21053 (p : Pattern) (guard : d9846 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9844 p = 1 := by simpa only [d9846, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21052 p hg
    simpa only [d9846, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9846, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d9846, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21054 (p : Pattern) (guard : d14770 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14770, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d14770, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9846 p = 1 := by simpa only [d14770, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21053 p hg
    simpa only [d14770, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21055 (p : Pattern) (guard : d14771 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14770 p = 1 := by simpa only [d14771, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21054 p hg
    simpa only [d14771, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14771, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d14771, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21056 (p : Pattern) (guard : d14772 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14771 p = 1 := by simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21055 p hg
    simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20467 p hg
    simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21057 (p : Pattern) (guard : d14773 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5022 p = 1 := by simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21050 p hg
    simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14772 p = 1 := by simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21056 p hg
    simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21058 (p : Pattern) (guard : d16447 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21041 p hg
    simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14773 p = 1 := by simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21057 p hg
    simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21059 (p : Pattern) (guard : d16448 p = 1) : d48346 p ≤ (0 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16448, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20458 p hg
    simpa only [d16448, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16447 p = 1 := by simpa only [d16448, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21058 p hg
    simpa only [d16448, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21060 (p : Pattern) (guard : d16449 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16449, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20457 p hg
    simpa only [d16449, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16448 p = 1 := by simpa only [d16449, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21059 p hg
    simpa only [d16449, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21061 (p : Pattern) (guard : d16450 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16446 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21044 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16449 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21060 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21062 (p : Pattern) (guard : d1127 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1124 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21038 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20467 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21063 (p : Pattern) (guard : d14778 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1127 p = 1 := by simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21062 p hg
    simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14772 p = 1 := by simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21056 p hg
    simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21064 (p : Pattern) (guard : d16451 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21041 p hg
    simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14778 p = 1 := by simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21063 p hg
    simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21065 (p : Pattern) (guard : d16452 p = 1) : d48346 p ≤ (0 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16452, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20458 p hg
    simpa only [d16452, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16451 p = 1 := by simpa only [d16452, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21064 p hg
    simpa only [d16452, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21066 (p : Pattern) (guard : d16453 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16453, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20457 p hg
    simpa only [d16453, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16452 p = 1 := by simpa only [d16453, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21065 p hg
    simpa only [d16453, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21067 (p : Pattern) (guard : d16454 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16453 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21066 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20473 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21068 (p : Pattern) (guard : d16455 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16450 p = 1 := by simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21061 p hg
    simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16454 p = 1 := by simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21067 p hg
    simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21069 (p : Pattern) (guard : d16456 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16455 p = 1 := by simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21068 p hg
    simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20473 p hg
    simpa only [d16456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21070 (p : Pattern) (guard : d16457 p = 1) : d48356 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16456 p = 1 := by simpa only [d16457, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21069 p hg
    simpa only [d16457, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16457, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20477 p hg
    simpa only [d16457, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21071 (p : Pattern) (guard : d16458 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16458, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20456 p hg
    simpa only [d16458, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16457 p = 1 := by simpa only [d16458, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21070 p hg
    simpa only [d16458, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21072 (p : Pattern) (guard : d16459 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16454 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21067 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20473 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21073 (p : Pattern) (guard : d16460 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16459 p = 1 := by simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21072 p hg
    simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20473 p hg
    simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21074 (p : Pattern) (guard : d16461 p = 1) : d48356 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16460 p = 1 := by simpa only [d16461, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21073 p hg
    simpa only [d16461, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16461, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20477 p hg
    simpa only [d16461, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21075 (p : Pattern) (guard : d16462 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16462, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20456 p hg
    simpa only [d16462, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16461 p = 1 := by simpa only [d16462, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21074 p hg
    simpa only [d16462, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21076 (p : Pattern) (guard : d16463 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16458 p = 1 := by simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21071 p hg
    simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16462 p = 1 := by simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21075 p hg
    simpa only [d16463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21077 (p : Pattern) (guard : d16464 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16463 p = 1 := by simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21076 p hg
    simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21078 (p : Pattern) (guard : d16465 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16464 p = 1 := by simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21077 p hg
    simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21079 (p : Pattern) (guard : d16479 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16465 p = 1 := by simpa only [d16479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21078 p hg
    simpa only [d16479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21080 (p : Pattern) (guard : d16467 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16462 p = 1 := by simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21075 p hg
    simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21081 (p : Pattern) (guard : d16468 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16467 p = 1 := by simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21080 p hg
    simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21082 (p : Pattern) (guard : d16469 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16468 p = 1 := by simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21081 p hg
    simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21083 (p : Pattern) (guard : d16480 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16469 p = 1 := by simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21082 p hg
    simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21084 (p : Pattern) (guard : d16481 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16479 p = 1 := by simpa only [d16481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21079 p hg
    simpa only [d16481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16480 p = 1 := by simpa only [d16481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21083 p hg
    simpa only [d16481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21085 (p : Pattern) (guard : d16482 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16481 p = 1 := by simpa only [d16482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21084 p hg
    simpa only [d16482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21086 (p : Pattern) (guard : d16483 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16482 p = 1 := by simpa only [d16483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21085 p hg
    simpa only [d16483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21087 (p : Pattern) (guard : d16484 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16483 p = 1 := by simpa only [d16484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21086 p hg
    simpa only [d16484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21088 (p : Pattern) (guard : d16485 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16484 p = 1 := by simpa only [d16485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21087 p hg
    simpa only [d16485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21089 (p : Pattern) (guard : d171133 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171133, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d171133, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16485 p = 1 := by simpa only [d171133, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21088 p hg
    simpa only [d171133, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21090 (p : Pattern) (guard : d171134 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d171134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171133 p = 1 := by simpa only [d171134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21089 p hg
    simpa only [d171134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21091 (p : Pattern) (guard : d171135 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 69 with
  | false =>
    have hg : d171134 p = 1 := by simpa only [d171135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21090 p hg
    simpa only [d171135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d171135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21092 (p : Pattern) (guard : d171136 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 51 with
  | false =>
    have hg : d171135 p = 1 := by simpa only [d171136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21091 p hg
    simpa only [d171136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d171136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21093 (p : Pattern) (guard : d171137 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 50 with
  | false =>
    have hg : d171136 p = 1 := by simpa only [d171137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21092 p hg
    simpa only [d171137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d171137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21094 (p : Pattern) (guard : d171138 p = 1) : d48359 p ≤ (0 : Int) + d173727 p := by
  cases selected : p 49 with
  | false =>
    have hg : d171132 p = 1 := by simpa only [d171138, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21005 p hg
    simpa only [d171138, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171137 p = 1 := by simpa only [d171138, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21093 p hg
    simpa only [d171138, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21095 (p : Pattern) (guard : d175680 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 48 with
  | false =>
    have hg : d171138 p = 1 := by simpa only [d175680, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21094 p hg
    simpa only [d175680, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175680, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20495 p hg
    simpa only [d175680, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21096 (p : Pattern) (guard : d175681 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175680 p = 1 := by simpa only [d175681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21095 p hg
    simpa only [d175681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21097 (p : Pattern) (guard : d175682 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175681 p = 1 := by simpa only [d175682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21096 p hg
    simpa only [d175682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21098 (p : Pattern) (guard : d175683 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175682 p = 1 := by simpa only [d175683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21097 p hg
    simpa only [d175683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21099 (p : Pattern) (guard : d175684 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175683 p = 1 := by simpa only [d175684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d175684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21100 (p : Pattern) (guard : d175685 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175684 p = 1 := by simpa only [d175685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21099 p hg
    simpa only [d175685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21101 (p : Pattern) (guard : d175686 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175685 p = 1 := by simpa only [d175686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21100 p hg
    simpa only [d175686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21102 (p : Pattern) (guard : d175687 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175686 p = 1 := by simpa only [d175687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21101 p hg
    simpa only [d175687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21103 (p : Pattern) (guard : d175688 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175687 p = 1 := by simpa only [d175688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21102 p hg
    simpa only [d175688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21104 (p : Pattern) (guard : d175689 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d175679 p = 1 := by simpa only [d175689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20883 p hg
    simpa only [d175689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175688 p = 1 := by simpa only [d175689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21103 p hg
    simpa only [d175689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21105 (p : Pattern) (guard : d1554 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare21106 (p : Pattern) (guard : d1555 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1554 p = 1 := by simpa only [d1555, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21105 p hg
    simpa only [d1555, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1555, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d1555, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21107 (p : Pattern) (guard : d1556 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1555 p = 1 := by simpa only [d1556, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21106 p hg
    simpa only [d1556, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1556, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d1556, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21108 (p : Pattern) (guard : d1557 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1557, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d1557, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1556 p = 1 := by simpa only [d1557, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21107 p hg
    simpa only [d1557, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21109 (p : Pattern) (guard : d1558 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1557 p = 1 := by simpa only [d1558, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21108 p hg
    simpa only [d1558, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1558, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d1558, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21110 (p : Pattern) (guard : d10073 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare21111 (p : Pattern) (guard : d10074 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10073 p = 1 := by simpa only [d10074, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21110 p hg
    simpa only [d10074, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10074, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d10074, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21112 (p : Pattern) (guard : d10076 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10074 p = 1 := by simpa only [d10076, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21111 p hg
    simpa only [d10076, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10076, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d10076, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21113 (p : Pattern) (guard : d16787 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16787, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d16787, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10076 p = 1 := by simpa only [d16787, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21112 p hg
    simpa only [d16787, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21114 (p : Pattern) (guard : d16788 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16787 p = 1 := by simpa only [d16788, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21113 p hg
    simpa only [d16788, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16788, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d16788, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21115 (p : Pattern) (guard : d16789 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1558 p = 1 := by simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21109 p hg
    simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16788 p = 1 := by simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21114 p hg
    simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21116 (p : Pattern) (guard : d10062 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare21117 (p : Pattern) (guard : d10063 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10062 p = 1 := by simpa only [d10063, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21116 p hg
    simpa only [d10063, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10063, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d10063, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21118 (p : Pattern) (guard : d10065 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10063 p = 1 := by simpa only [d10065, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21117 p hg
    simpa only [d10065, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10065, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d10065, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21119 (p : Pattern) (guard : d15151 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15151, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d15151, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10065 p = 1 := by simpa only [d15151, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21118 p hg
    simpa only [d15151, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21120 (p : Pattern) (guard : d15152 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15151 p = 1 := by simpa only [d15152, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21119 p hg
    simpa only [d15152, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15152, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d15152, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21121 (p : Pattern) (guard : d10084 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare21122 (p : Pattern) (guard : d10085 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10084 p = 1 := by simpa only [d10085, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21121 p hg
    simpa only [d10085, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10085, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d10085, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21123 (p : Pattern) (guard : d10087 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10085 p = 1 := by simpa only [d10087, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21122 p hg
    simpa only [d10087, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10087, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d10087, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21124 (p : Pattern) (guard : d15156 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15156, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d15156, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10087 p = 1 := by simpa only [d15156, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21123 p hg
    simpa only [d15156, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21125 (p : Pattern) (guard : d15157 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15156 p = 1 := by simpa only [d15157, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21124 p hg
    simpa only [d15157, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15157, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d15157, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21126 (p : Pattern) (guard : d16790 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15152 p = 1 := by simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21120 p hg
    simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15157 p = 1 := by simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21125 p hg
    simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21127 (p : Pattern) (guard : d16791 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16789 p = 1 := by simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21115 p hg
    simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16790 p = 1 := by simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21126 p hg
    simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21128 (p : Pattern) (guard : d1569 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare21129 (p : Pattern) (guard : d1570 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1569 p = 1 := by simpa only [d1570, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21128 p hg
    simpa only [d1570, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1570, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d1570, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21130 (p : Pattern) (guard : d1571 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1570 p = 1 := by simpa only [d1571, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21129 p hg
    simpa only [d1571, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1571, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d1571, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21131 (p : Pattern) (guard : d1572 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1572, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d1572, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1571 p = 1 := by simpa only [d1572, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21130 p hg
    simpa only [d1572, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21132 (p : Pattern) (guard : d1573 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1572 p = 1 := by simpa only [d1573, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21131 p hg
    simpa only [d1573, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1573, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d1573, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21133 (p : Pattern) (guard : d10114 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare21134 (p : Pattern) (guard : d10115 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10114 p = 1 := by simpa only [d10115, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21133 p hg
    simpa only [d10115, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10115, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d10115, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21135 (p : Pattern) (guard : d10117 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10115 p = 1 := by simpa only [d10117, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21134 p hg
    simpa only [d10117, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10117, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d10117, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21136 (p : Pattern) (guard : d16792 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16792, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d16792, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10117 p = 1 := by simpa only [d16792, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21135 p hg
    simpa only [d16792, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21137 (p : Pattern) (guard : d16793 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16792 p = 1 := by simpa only [d16793, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21136 p hg
    simpa only [d16793, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16793, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d16793, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21138 (p : Pattern) (guard : d16794 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1573 p = 1 := by simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21132 p hg
    simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16793 p = 1 := by simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21137 p hg
    simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21139 (p : Pattern) (guard : d15158 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15157 p = 1 := by simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21125 p hg
    simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20402 p hg
    simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21140 (p : Pattern) (guard : d16795 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16794 p = 1 := by simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21138 p hg
    simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15158 p = 1 := by simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21139 p hg
    simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21141 (p : Pattern) (guard : d16796 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16791 p = 1 := by simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21127 p hg
    simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16795 p = 1 := by simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21140 p hg
    simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21142 (p : Pattern) (guard : d16797 p = 1) : d48326 p ≤ (0 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16797, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20392 p hg
    simpa only [d16797, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16796 p = 1 := by simpa only [d16797, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21141 p hg
    simpa only [d16797, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21143 (p : Pattern) (guard : d16798 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16798, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20391 p hg
    simpa only [d16798, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16797 p = 1 := by simpa only [d16798, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21142 p hg
    simpa only [d16798, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21144 (p : Pattern) (guard : d5133 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare21145 (p : Pattern) (guard : d5134 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5133 p = 1 := by simpa only [d5134, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21144 p hg
    simpa only [d5134, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5134, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d5134, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21146 (p : Pattern) (guard : d5135 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5134 p = 1 := by simpa only [d5135, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21145 p hg
    simpa only [d5135, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5135, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d5135, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21147 (p : Pattern) (guard : d5136 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5136, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d5136, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5135 p = 1 := by simpa only [d5136, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21146 p hg
    simpa only [d5136, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21148 (p : Pattern) (guard : d5137 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5136 p = 1 := by simpa only [d5137, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21147 p hg
    simpa only [d5137, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5137, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d5137, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21149 (p : Pattern) (guard : d5138 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5137 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21148 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20402 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21150 (p : Pattern) (guard : d10134 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare21151 (p : Pattern) (guard : d10135 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10134 p = 1 := by simpa only [d10135, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21150 p hg
    simpa only [d10135, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10135, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d10135, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21152 (p : Pattern) (guard : d10137 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10135 p = 1 := by simpa only [d10137, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21151 p hg
    simpa only [d10137, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10137, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d10137, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21153 (p : Pattern) (guard : d15163 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15163, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d15163, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10137 p = 1 := by simpa only [d15163, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21152 p hg
    simpa only [d15163, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21154 (p : Pattern) (guard : d15164 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15163 p = 1 := by simpa only [d15164, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21153 p hg
    simpa only [d15164, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15164, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d15164, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21155 (p : Pattern) (guard : d15165 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15164 p = 1 := by simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21154 p hg
    simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20402 p hg
    simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21156 (p : Pattern) (guard : d15166 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5138 p = 1 := by simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21149 p hg
    simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15165 p = 1 := by simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21155 p hg
    simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21157 (p : Pattern) (guard : d16799 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21140 p hg
    simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15166 p = 1 := by simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21156 p hg
    simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21158 (p : Pattern) (guard : d16800 p = 1) : d48326 p ≤ (0 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16800, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20392 p hg
    simpa only [d16800, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16799 p = 1 := by simpa only [d16800, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21157 p hg
    simpa only [d16800, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21159 (p : Pattern) (guard : d16801 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16801, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20391 p hg
    simpa only [d16801, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16800 p = 1 := by simpa only [d16801, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21158 p hg
    simpa only [d16801, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21160 (p : Pattern) (guard : d16802 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16798 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21143 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16801 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21159 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21161 (p : Pattern) (guard : d1581 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare21162 (p : Pattern) (guard : d1582 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1581 p = 1 := by simpa only [d1582, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21161 p hg
    simpa only [d1582, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1582, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d1582, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21163 (p : Pattern) (guard : d1583 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1582 p = 1 := by simpa only [d1583, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21162 p hg
    simpa only [d1583, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1583, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d1583, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21164 (p : Pattern) (guard : d1584 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1584, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d1584, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1583 p = 1 := by simpa only [d1584, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21163 p hg
    simpa only [d1584, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21165 (p : Pattern) (guard : d1585 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1584 p = 1 := by simpa only [d1585, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21164 p hg
    simpa only [d1585, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1585, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d1585, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21166 (p : Pattern) (guard : d1588 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1585 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21165 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20402 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21167 (p : Pattern) (guard : d15171 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1588 p = 1 := by simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21166 p hg
    simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15165 p = 1 := by simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21155 p hg
    simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21168 (p : Pattern) (guard : d16803 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21140 p hg
    simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15171 p = 1 := by simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21167 p hg
    simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21169 (p : Pattern) (guard : d16804 p = 1) : d48326 p ≤ (0 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16804, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20392 p hg
    simpa only [d16804, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16803 p = 1 := by simpa only [d16804, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21168 p hg
    simpa only [d16804, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21170 (p : Pattern) (guard : d16805 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16805, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20391 p hg
    simpa only [d16805, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16804 p = 1 := by simpa only [d16805, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21169 p hg
    simpa only [d16805, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21171 (p : Pattern) (guard : d16806 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16805 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21170 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20408 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21172 (p : Pattern) (guard : d16807 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16802 p = 1 := by simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21160 p hg
    simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16806 p = 1 := by simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21171 p hg
    simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21173 (p : Pattern) (guard : d16808 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16807 p = 1 := by simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21172 p hg
    simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20408 p hg
    simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21174 (p : Pattern) (guard : d16809 p = 1) : d48338 p ≤ (0 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16808 p = 1 := by simpa only [d16809, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21173 p hg
    simpa only [d16809, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16809, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d16809, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21175 (p : Pattern) (guard : d16810 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16810, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20390 p hg
    simpa only [d16810, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16809 p = 1 := by simpa only [d16810, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21174 p hg
    simpa only [d16810, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21176 (p : Pattern) (guard : d16811 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16806 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21171 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20408 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21177 (p : Pattern) (guard : d16812 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16811 p = 1 := by simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21176 p hg
    simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20408 p hg
    simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21178 (p : Pattern) (guard : d16813 p = 1) : d48338 p ≤ (0 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16812 p = 1 := by simpa only [d16813, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21177 p hg
    simpa only [d16813, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16813, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d16813, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21179 (p : Pattern) (guard : d16814 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16814, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20390 p hg
    simpa only [d16814, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16813 p = 1 := by simpa only [d16814, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21178 p hg
    simpa only [d16814, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21180 (p : Pattern) (guard : d16815 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16810 p = 1 := by simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21175 p hg
    simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16814 p = 1 := by simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21179 p hg
    simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21181 (p : Pattern) (guard : d16816 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16815 p = 1 := by simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21180 p hg
    simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21182 (p : Pattern) (guard : d16817 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16816 p = 1 := by simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21181 p hg
    simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21183 (p : Pattern) (guard : d16818 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16817 p = 1 := by simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21182 p hg
    simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21184 (p : Pattern) (guard : d16819 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16814 p = 1 := by simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21179 p hg
    simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21185 (p : Pattern) (guard : d16820 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16819 p = 1 := by simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21184 p hg
    simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21186 (p : Pattern) (guard : d16821 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16820 p = 1 := by simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21185 p hg
    simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21187 (p : Pattern) (guard : d16822 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16821 p = 1 := by simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21186 p hg
    simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21188 (p : Pattern) (guard : d16823 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16818 p = 1 := by simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21183 p hg
    simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16822 p = 1 := by simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21187 p hg
    simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21189 (p : Pattern) (guard : d16824 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16823 p = 1 := by simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21188 p hg
    simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21190 (p : Pattern) (guard : d16825 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16824 p = 1 := by simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21189 p hg
    simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21191 (p : Pattern) (guard : d16826 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16825 p = 1 := by simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21190 p hg
    simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21192 (p : Pattern) (guard : d16827 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16826 p = 1 := by simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21191 p hg
    simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21193 (p : Pattern) (guard : d16828 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16828, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16828, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16827 p = 1 := by simpa only [d16828, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21192 p hg
    simpa only [d16828, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21194 (p : Pattern) (guard : d16798 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16798, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20426 p hg
    simpa only [d16798, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16797 p = 1 := by simpa only [d16798, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21142 p hg
    simpa only [d16798, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21195 (p : Pattern) (guard : d16801 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16801, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20426 p hg
    simpa only [d16801, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16800 p = 1 := by simpa only [d16801, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21158 p hg
    simpa only [d16801, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21196 (p : Pattern) (guard : d16802 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16798 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21194 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16801 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21195 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21197 (p : Pattern) (guard : d16805 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16805, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20426 p hg
    simpa only [d16805, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16804 p = 1 := by simpa only [d16805, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21169 p hg
    simpa only [d16805, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21198 (p : Pattern) (guard : d16806 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16805 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21197 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20428 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21199 (p : Pattern) (guard : d16807 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16802 p = 1 := by simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21196 p hg
    simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16806 p = 1 := by simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21198 p hg
    simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21200 (p : Pattern) (guard : d16808 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16807 p = 1 := by simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21199 p hg
    simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20428 p hg
    simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21201 (p : Pattern) (guard : d16809 p = 1) : d48329 p ≤ (0 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16808 p = 1 := by simpa only [d16809, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21200 p hg
    simpa only [d16809, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16809, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d16809, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21202 (p : Pattern) (guard : d16810 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16810, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20425 p hg
    simpa only [d16810, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16809 p = 1 := by simpa only [d16810, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21201 p hg
    simpa only [d16810, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21203 (p : Pattern) (guard : d16811 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16806 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21198 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20428 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21204 (p : Pattern) (guard : d16812 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16811 p = 1 := by simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21203 p hg
    simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20428 p hg
    simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21205 (p : Pattern) (guard : d16813 p = 1) : d48329 p ≤ (0 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16812 p = 1 := by simpa only [d16813, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21204 p hg
    simpa only [d16813, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16813, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d16813, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21206 (p : Pattern) (guard : d16814 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16814, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20425 p hg
    simpa only [d16814, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16813 p = 1 := by simpa only [d16814, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21205 p hg
    simpa only [d16814, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21207 (p : Pattern) (guard : d16815 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16810 p = 1 := by simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21202 p hg
    simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16814 p = 1 := by simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21206 p hg
    simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21208 (p : Pattern) (guard : d16816 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16815 p = 1 := by simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21207 p hg
    simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21209 (p : Pattern) (guard : d16817 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16816 p = 1 := by simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21208 p hg
    simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21210 (p : Pattern) (guard : d16818 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16817 p = 1 := by simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21209 p hg
    simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21211 (p : Pattern) (guard : d16819 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16814 p = 1 := by simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21206 p hg
    simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21212 (p : Pattern) (guard : d16820 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16819 p = 1 := by simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21211 p hg
    simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21213 (p : Pattern) (guard : d16821 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16820 p = 1 := by simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21212 p hg
    simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21214 (p : Pattern) (guard : d16822 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16821 p = 1 := by simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21213 p hg
    simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21215 (p : Pattern) (guard : d16823 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16818 p = 1 := by simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21210 p hg
    simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16822 p = 1 := by simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21214 p hg
    simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21216 (p : Pattern) (guard : d16824 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16823 p = 1 := by simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21215 p hg
    simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21217 (p : Pattern) (guard : d16825 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16824 p = 1 := by simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21216 p hg
    simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21218 (p : Pattern) (guard : d16826 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16825 p = 1 := by simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21217 p hg
    simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21219 (p : Pattern) (guard : d16827 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16826 p = 1 := by simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21218 p hg
    simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21220 (p : Pattern) (guard : d16831 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16817 p = 1 := by simpa only [d16831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21182 p hg
    simpa only [d16831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21221 (p : Pattern) (guard : d16832 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16821 p = 1 := by simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21186 p hg
    simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21222 (p : Pattern) (guard : d16833 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16831 p = 1 := by simpa only [d16833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21220 p hg
    simpa only [d16833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16832 p = 1 := by simpa only [d16833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21221 p hg
    simpa only [d16833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21223 (p : Pattern) (guard : d16834 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16833 p = 1 := by simpa only [d16834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21222 p hg
    simpa only [d16834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21224 (p : Pattern) (guard : d16835 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16834 p = 1 := by simpa only [d16835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21223 p hg
    simpa only [d16835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21225 (p : Pattern) (guard : d16836 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16835 p = 1 := by simpa only [d16836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21224 p hg
    simpa only [d16836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21226 (p : Pattern) (guard : d16837 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d16837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16836 p = 1 := by simpa only [d16837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21225 p hg
    simpa only [d16837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21227 (p : Pattern) (guard : d16838 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16827 p = 1 := by simpa only [d16838, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21219 p hg
    simpa only [d16838, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16837 p = 1 := by simpa only [d16838, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21226 p hg
    simpa only [d16838, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21228 (p : Pattern) (guard : d16839 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d16828 p = 1 := by simpa only [d16839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21193 p hg
    simpa only [d16839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16838 p = 1 := by simpa only [d16839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21227 p hg
    simpa only [d16839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21229 (p : Pattern) (guard : d16840 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d16839 p = 1 := by simpa only [d16840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21228 p hg
    simpa only [d16840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20387 p hg
    simpa only [d16840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21230 (p : Pattern) (guard : d171168 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 51 with
  | false =>
    have hg : d16840 p = 1 := by simpa only [d171168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21229 p hg
    simpa only [d171168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20387 p hg
    simpa only [d171168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21231 (p : Pattern) (guard : d171169 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20387 p hg
    simpa only [d171169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171168 p = 1 := by simpa only [d171169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21230 p hg
    simpa only [d171169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21232 (p : Pattern) (guard : d1554 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21233 (p : Pattern) (guard : d1555 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1554 p = 1 := by simpa only [d1555, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21232 p hg
    simpa only [d1555, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1555, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d1555, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21234 (p : Pattern) (guard : d1556 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1555 p = 1 := by simpa only [d1556, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21233 p hg
    simpa only [d1556, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1556, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d1556, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21235 (p : Pattern) (guard : d1557 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1557, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d1557, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1556 p = 1 := by simpa only [d1557, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21234 p hg
    simpa only [d1557, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21236 (p : Pattern) (guard : d1558 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1557 p = 1 := by simpa only [d1558, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21235 p hg
    simpa only [d1558, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1558, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d1558, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21237 (p : Pattern) (guard : d10073 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21238 (p : Pattern) (guard : d10074 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10073 p = 1 := by simpa only [d10074, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21237 p hg
    simpa only [d10074, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10074, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d10074, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21239 (p : Pattern) (guard : d10076 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10074 p = 1 := by simpa only [d10076, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21238 p hg
    simpa only [d10076, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10076, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d10076, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21240 (p : Pattern) (guard : d16787 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16787, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d16787, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10076 p = 1 := by simpa only [d16787, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21239 p hg
    simpa only [d16787, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21241 (p : Pattern) (guard : d16788 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16787 p = 1 := by simpa only [d16788, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21240 p hg
    simpa only [d16788, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16788, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d16788, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21242 (p : Pattern) (guard : d16789 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1558 p = 1 := by simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21236 p hg
    simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16788 p = 1 := by simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21241 p hg
    simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21243 (p : Pattern) (guard : d10062 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21244 (p : Pattern) (guard : d10063 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10062 p = 1 := by simpa only [d10063, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21243 p hg
    simpa only [d10063, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10063, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d10063, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21245 (p : Pattern) (guard : d10065 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10063 p = 1 := by simpa only [d10065, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21244 p hg
    simpa only [d10065, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10065, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d10065, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21246 (p : Pattern) (guard : d15151 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15151, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d15151, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10065 p = 1 := by simpa only [d15151, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21245 p hg
    simpa only [d15151, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21247 (p : Pattern) (guard : d15152 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15151 p = 1 := by simpa only [d15152, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21246 p hg
    simpa only [d15152, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15152, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d15152, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21248 (p : Pattern) (guard : d10084 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21249 (p : Pattern) (guard : d10085 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10084 p = 1 := by simpa only [d10085, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21248 p hg
    simpa only [d10085, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10085, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d10085, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
