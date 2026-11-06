import NetHack.Soko22Hazard87.Compare189
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare47500 (p : Pattern) (guard : d369699 p = 1) : d50664 p ≤ (1 : Int) + d367868 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369699, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46709 p hg
    simpa only [d369699, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369698 p = 1 := by simpa only [d369699, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47499 p hg
    simpa only [d369699, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47501 (p : Pattern) (guard : d369700 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369700, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46708 p hg
    simpa only [d369700, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369699 p = 1 := by simpa only [d369700, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47500 p hg
    simpa only [d369700, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47502 (p : Pattern) (guard : d369701 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369516 p = 1 := by simpa only [d369701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47193 p hg
    simpa only [d369701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275509 p = 1 := by simpa only [d369701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46732 p hg
    simpa only [d369701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47503 (p : Pattern) (guard : d369702 p = 1) : d50663 p ≤ (1 : Int) + d367867 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369517 p = 1 := by simpa only [d369702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47194 p hg
    simpa only [d369702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369701 p = 1 := by simpa only [d369702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47502 p hg
    simpa only [d369702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47504 (p : Pattern) (guard : d369703 p = 1) : d50664 p ≤ (1 : Int) + d367868 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369703, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46709 p hg
    simpa only [d369703, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369702 p = 1 := by simpa only [d369703, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47503 p hg
    simpa only [d369703, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47505 (p : Pattern) (guard : d369704 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369704, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46708 p hg
    simpa only [d369704, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369703 p = 1 := by simpa only [d369704, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47504 p hg
    simpa only [d369704, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47506 (p : Pattern) (guard : d369705 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369700 p = 1 := by simpa only [d369705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47501 p hg
    simpa only [d369705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369704 p = 1 := by simpa only [d369705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47505 p hg
    simpa only [d369705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47507 (p : Pattern) (guard : d369706 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369705 p = 1 := by simpa only [d369706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47506 p hg
    simpa only [d369706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369521 p = 1 := by simpa only [d369706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47198 p hg
    simpa only [d369706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47508 (p : Pattern) (guard : d369707 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369706 p = 1 := by simpa only [d369707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47507 p hg
    simpa only [d369707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46737 p hg
    simpa only [d369707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47509 (p : Pattern) (guard : d369708 p = 1) : d50673 p ≤ (1 : Int) + d367877 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369707 p = 1 := by simpa only [d369708, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47508 p hg
    simpa only [d369708, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369708, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46741 p hg
    simpa only [d369708, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47510 (p : Pattern) (guard : d369709 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369709, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46707 p hg
    simpa only [d369709, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369708 p = 1 := by simpa only [d369709, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47509 p hg
    simpa only [d369709, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47511 (p : Pattern) (guard : d369623 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369399 p = 1 := by simpa only [d369623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46956 p hg
    simpa only [d369623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46737 p hg
    simpa only [d369623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47512 (p : Pattern) (guard : d369624 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369521 p = 1 := by simpa only [d369624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47198 p hg
    simpa only [d369624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369623 p = 1 := by simpa only [d369624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47511 p hg
    simpa only [d369624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47513 (p : Pattern) (guard : d369625 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369624 p = 1 := by simpa only [d369625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47512 p hg
    simpa only [d369625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46737 p hg
    simpa only [d369625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47514 (p : Pattern) (guard : d369626 p = 1) : d50673 p ≤ (1 : Int) + d367877 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369625 p = 1 := by simpa only [d369626, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47513 p hg
    simpa only [d369626, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369626, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46741 p hg
    simpa only [d369626, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47515 (p : Pattern) (guard : d369627 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369627, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46707 p hg
    simpa only [d369627, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369626 p = 1 := by simpa only [d369627, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47514 p hg
    simpa only [d369627, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47516 (p : Pattern) (guard : d369710 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369709 p = 1 := by simpa only [d369710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47510 p hg
    simpa only [d369710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369627 p = 1 := by simpa only [d369710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47515 p hg
    simpa only [d369710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47517 (p : Pattern) (guard : d369711 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369710 p = 1 := by simpa only [d369711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47516 p hg
    simpa only [d369711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47518 (p : Pattern) (guard : d369712 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369711 p = 1 := by simpa only [d369712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47517 p hg
    simpa only [d369712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47519 (p : Pattern) (guard : d369737 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369712 p = 1 := by simpa only [d369737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47518 p hg
    simpa only [d369737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47520 (p : Pattern) (guard : d369628 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369623 p = 1 := by simpa only [d369628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47511 p hg
    simpa only [d369628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46737 p hg
    simpa only [d369628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47521 (p : Pattern) (guard : d369629 p = 1) : d50665 p ≤ (1 : Int) + d367869 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369628 p = 1 := by simpa only [d369629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47520 p hg
    simpa only [d369629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46737 p hg
    simpa only [d369629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47522 (p : Pattern) (guard : d369630 p = 1) : d50673 p ≤ (1 : Int) + d367877 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369629 p = 1 := by simpa only [d369630, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47521 p hg
    simpa only [d369630, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369630, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46741 p hg
    simpa only [d369630, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47523 (p : Pattern) (guard : d369631 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369631, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46707 p hg
    simpa only [d369631, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369630 p = 1 := by simpa only [d369631, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47522 p hg
    simpa only [d369631, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47524 (p : Pattern) (guard : d369632 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369627 p = 1 := by simpa only [d369632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47515 p hg
    simpa only [d369632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369631 p = 1 := by simpa only [d369632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47523 p hg
    simpa only [d369632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47525 (p : Pattern) (guard : d369633 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369632 p = 1 := by simpa only [d369633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47524 p hg
    simpa only [d369633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47526 (p : Pattern) (guard : d369634 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369633 p = 1 := by simpa only [d369634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47525 p hg
    simpa only [d369634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47527 (p : Pattern) (guard : d369648 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369634 p = 1 := by simpa only [d369648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47526 p hg
    simpa only [d369648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47528 (p : Pattern) (guard : d369738 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369737 p = 1 := by simpa only [d369738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47519 p hg
    simpa only [d369738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369648 p = 1 := by simpa only [d369738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47527 p hg
    simpa only [d369738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47529 (p : Pattern) (guard : d369739 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369738 p = 1 := by simpa only [d369739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47528 p hg
    simpa only [d369739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47530 (p : Pattern) (guard : d369716 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369627 p = 1 := by simpa only [d369716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47515 p hg
    simpa only [d369716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47531 (p : Pattern) (guard : d369717 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369716 p = 1 := by simpa only [d369717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47530 p hg
    simpa only [d369717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47532 (p : Pattern) (guard : d369718 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369717 p = 1 := by simpa only [d369718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47531 p hg
    simpa only [d369718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47533 (p : Pattern) (guard : d369740 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369718 p = 1 := by simpa only [d369740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47532 p hg
    simpa only [d369740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47534 (p : Pattern) (guard : d369741 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369740 p = 1 := by simpa only [d369741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47533 p hg
    simpa only [d369741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47535 (p : Pattern) (guard : d369742 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369741 p = 1 := by simpa only [d369742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47534 p hg
    simpa only [d369742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47536 (p : Pattern) (guard : d369743 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369739 p = 1 := by simpa only [d369743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47529 p hg
    simpa only [d369743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369742 p = 1 := by simpa only [d369743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47535 p hg
    simpa only [d369743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47537 (p : Pattern) (guard : d369764 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369743 p = 1 := by simpa only [d369764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47536 p hg
    simpa only [d369764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47538 (p : Pattern) (guard : d369765 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369764 p = 1 := by simpa only [d369765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47537 p hg
    simpa only [d369765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47539 (p : Pattern) (guard : d369766 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369766, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369766, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369765 p = 1 := by simpa only [d369766, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47538 p hg
    simpa only [d369766, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47540 (p : Pattern) (guard : d369767 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46705 p hg
    simpa only [d369767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369766 p = 1 := by simpa only [d369767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47539 p hg
    simpa only [d369767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47541 (p : Pattern) (guard : d369636 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369631 p = 1 := by simpa only [d369636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47523 p hg
    simpa only [d369636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47542 (p : Pattern) (guard : d369637 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369636 p = 1 := by simpa only [d369637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47541 p hg
    simpa only [d369637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47543 (p : Pattern) (guard : d369638 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369637 p = 1 := by simpa only [d369638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47542 p hg
    simpa only [d369638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47544 (p : Pattern) (guard : d369649 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369638 p = 1 := by simpa only [d369649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47543 p hg
    simpa only [d369649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47545 (p : Pattern) (guard : d369754 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369649 p = 1 := by simpa only [d369754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47544 p hg
    simpa only [d369754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47546 (p : Pattern) (guard : d369755 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369754 p = 1 := by simpa only [d369755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47545 p hg
    simpa only [d369755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47547 (p : Pattern) (guard : d369756 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369755 p = 1 := by simpa only [d369756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47546 p hg
    simpa only [d369756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47548 (p : Pattern) (guard : d369757 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369756 p = 1 := by simpa only [d369757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47547 p hg
    simpa only [d369757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47549 (p : Pattern) (guard : d369758 p = 1) : d50674 p ≤ (1 : Int) + d367878 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46706 p hg
    simpa only [d369758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369757 p = 1 := by simpa only [d369758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47548 p hg
    simpa only [d369758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47550 (p : Pattern) (guard : d369768 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369768, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369768, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369758 p = 1 := by simpa only [d369768, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47549 p hg
    simpa only [d369768, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47551 (p : Pattern) (guard : d369769 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46705 p hg
    simpa only [d369769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369768 p = 1 := by simpa only [d369769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47550 p hg
    simpa only [d369769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47552 (p : Pattern) (guard : d369770 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 69 with
  | false =>
    have hg : d369767 p = 1 := by simpa only [d369770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47540 p hg
    simpa only [d369770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369769 p = 1 := by simpa only [d369770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47551 p hg
    simpa only [d369770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47553 (p : Pattern) (guard : d369771 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 51 with
  | false =>
    have hg : d369770 p = 1 := by simpa only [d369771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47552 p hg
    simpa only [d369771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46705 p hg
    simpa only [d369771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47554 (p : Pattern) (guard : d369772 p = 1) : d50675 p ≤ (1 : Int) + d367879 p := by
  cases selected : p 50 with
  | false =>
    have hg : d369771 p = 1 := by simpa only [d369772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47553 p hg
    simpa only [d369772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46705 p hg
    simpa only [d369772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47555 (p : Pattern) (guard : d369773 p = 1) : d50676 p ≤ (1 : Int) + d367880 p := by
  cases selected : p 49 with
  | false =>
    have hg : d369763 p = 1 := by simpa only [d369773, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47472 p hg
    simpa only [d369773, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369772 p = 1 := by simpa only [d369773, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47554 p hg
    simpa only [d369773, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47556 (p : Pattern) (guard : d46053 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39946 p hg
    simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46043 p = 1 := by simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47238 p hg
    simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47557 (p : Pattern) (guard : d46054 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 201 with
  | false =>
    have hg : d46053 p = 1 := by simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47556 p hg
    simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39946 p hg
    simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47558 (p : Pattern) (guard : d46055 p = 1) : d50560 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 182 with
  | false =>
    have hg : d46054 p = 1 := by simpa only [d46055, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47557 p hg
    simpa only [d46055, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46055, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46774 p hg
    simpa only [d46055, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47559 (p : Pattern) (guard : d179205 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39946 p hg
    simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179204 p = 1 := by simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46771 p hg
    simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47560 (p : Pattern) (guard : d369676 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369497 p = 1 := by simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47239 p hg
    simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179205 p = 1 := by simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47559 p hg
    simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47561 (p : Pattern) (guard : d369677 p = 1) : d50560 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369676 p = 1 := by simpa only [d369677, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47560 p hg
    simpa only [d369677, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369677, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46774 p hg
    simpa only [d369677, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47562 (p : Pattern) (guard : d369678 p = 1) : d50560 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 180 with
  | false =>
    have hg : d46055 p = 1 := by simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47558 p hg
    simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369677 p = 1 := by simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47561 p hg
    simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47563 (p : Pattern) (guard : d369774 p = 1) : d50726 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369774, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46763 p hg
    simpa only [d369774, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369678 p = 1 := by simpa only [d369774, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47562 p hg
    simpa only [d369774, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47564 (p : Pattern) (guard : d369679 p = 1) : d50727 p ≤ (1 : Int) + d367911 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369678 p = 1 := by simpa only [d369679, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47387 p hg
    simpa only [d369679, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369679, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46725 p hg
    simpa only [d369679, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47565 (p : Pattern) (guard : d369775 p = 1) : d50728 p ≤ (1 : Int) + d367912 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369774 p = 1 := by simpa only [d369775, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47563 p hg
    simpa only [d369775, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369679 p = 1 := by simpa only [d369775, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47564 p hg
    simpa only [d369775, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47566 (p : Pattern) (guard : d46053 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46043 p = 1 := by simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47255 p hg
    simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47567 (p : Pattern) (guard : d46054 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 201 with
  | false =>
    have hg : d46053 p = 1 := by simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47566 p hg
    simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47568 (p : Pattern) (guard : d46055 p = 1) : d50562 p ≤ (1 : Int) + d367794 p := by
  cases selected : p 182 with
  | false =>
    have hg : d46054 p = 1 := by simpa only [d46055, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47567 p hg
    simpa only [d46055, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46055, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46791 p hg
    simpa only [d46055, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47569 (p : Pattern) (guard : d179205 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179204 p = 1 := by simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46788 p hg
    simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47570 (p : Pattern) (guard : d369676 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369497 p = 1 := by simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47256 p hg
    simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179205 p = 1 := by simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47569 p hg
    simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47571 (p : Pattern) (guard : d369677 p = 1) : d50562 p ≤ (1 : Int) + d367794 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369676 p = 1 := by simpa only [d369677, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47570 p hg
    simpa only [d369677, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369677, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46791 p hg
    simpa only [d369677, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47572 (p : Pattern) (guard : d369678 p = 1) : d50562 p ≤ (1 : Int) + d367794 p := by
  cases selected : p 180 with
  | false =>
    have hg : d46055 p = 1 := by simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47568 p hg
    simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369677 p = 1 := by simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47571 p hg
    simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47573 (p : Pattern) (guard : d369679 p = 1) : d50573 p ≤ (1 : Int) + d367802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369678 p = 1 := by simpa only [d369679, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47572 p hg
    simpa only [d369679, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369679, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369679, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47574 (p : Pattern) (guard : d369680 p = 1) : d50574 p ≤ (1 : Int) + d367803 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369679 p = 1 := by simpa only [d369680, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47573 p hg
    simpa only [d369680, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369680, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369680, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47575 (p : Pattern) (guard : d369776 p = 1) : d50729 p ≤ (1 : Int) + d367913 p := by
  cases selected : p 161 with
  | false =>
    have hg : d369775 p = 1 := by simpa only [d369776, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47565 p hg
    simpa only [d369776, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369680 p = 1 := by simpa only [d369776, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47574 p hg
    simpa only [d369776, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47576 (p : Pattern) (guard : d369777 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369776 p = 1 := by simpa only [d369777, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47575 p hg
    simpa only [d369777, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369777, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46798 p hg
    simpa only [d369777, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47577 (p : Pattern) (guard : d369683 p = 1) : d50560 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369502 p = 1 := by simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47246 p hg
    simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369510 p = 1 := by simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47271 p hg
    simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47578 (p : Pattern) (guard : d369778 p = 1) : d50726 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369778, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46763 p hg
    simpa only [d369778, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369683 p = 1 := by simpa only [d369778, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47577 p hg
    simpa only [d369778, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47579 (p : Pattern) (guard : d369684 p = 1) : d50727 p ≤ (1 : Int) + d367911 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369683 p = 1 := by simpa only [d369684, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47392 p hg
    simpa only [d369684, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369684, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46725 p hg
    simpa only [d369684, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47580 (p : Pattern) (guard : d369779 p = 1) : d50728 p ≤ (1 : Int) + d367912 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369778 p = 1 := by simpa only [d369779, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47578 p hg
    simpa only [d369779, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369684 p = 1 := by simpa only [d369779, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47579 p hg
    simpa only [d369779, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47581 (p : Pattern) (guard : d369683 p = 1) : d50562 p ≤ (1 : Int) + d367794 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369502 p = 1 := by simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47263 p hg
    simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369510 p = 1 := by simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47277 p hg
    simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47582 (p : Pattern) (guard : d369684 p = 1) : d50573 p ≤ (1 : Int) + d367802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369683 p = 1 := by simpa only [d369684, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47581 p hg
    simpa only [d369684, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369684, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369684, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47583 (p : Pattern) (guard : d369685 p = 1) : d50574 p ≤ (1 : Int) + d367803 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369684 p = 1 := by simpa only [d369685, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47582 p hg
    simpa only [d369685, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369685, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369685, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47584 (p : Pattern) (guard : d369780 p = 1) : d50729 p ≤ (1 : Int) + d367913 p := by
  cases selected : p 161 with
  | false =>
    have hg : d369779 p = 1 := by simpa only [d369780, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47580 p hg
    simpa only [d369780, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369685 p = 1 := by simpa only [d369780, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47583 p hg
    simpa only [d369780, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47585 (p : Pattern) (guard : d369781 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369780 p = 1 := by simpa only [d369781, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47584 p hg
    simpa only [d369781, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369781, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46798 p hg
    simpa only [d369781, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47586 (p : Pattern) (guard : d369782 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369777 p = 1 := by simpa only [d369782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47576 p hg
    simpa only [d369782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369781 p = 1 := by simpa only [d369782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47585 p hg
    simpa only [d369782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47587 (p : Pattern) (guard : d369689 p = 1) : d50534 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369497 p = 1 := by simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47239 p hg
    simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39946 p hg
    simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47588 (p : Pattern) (guard : d369690 p = 1) : d50560 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369689 p = 1 := by simpa only [d369690, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47587 p hg
    simpa only [d369690, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369690, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46774 p hg
    simpa only [d369690, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47589 (p : Pattern) (guard : d369691 p = 1) : d50560 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369690 p = 1 := by simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47588 p hg
    simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369510 p = 1 := by simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47271 p hg
    simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47590 (p : Pattern) (guard : d369783 p = 1) : d50726 p ≤ (1 : Int) + d367780 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369783, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46763 p hg
    simpa only [d369783, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369691 p = 1 := by simpa only [d369783, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47589 p hg
    simpa only [d369783, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47591 (p : Pattern) (guard : d369692 p = 1) : d50727 p ≤ (1 : Int) + d367911 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369691 p = 1 := by simpa only [d369692, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47400 p hg
    simpa only [d369692, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369692, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46725 p hg
    simpa only [d369692, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47592 (p : Pattern) (guard : d369784 p = 1) : d50728 p ≤ (1 : Int) + d367912 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369783 p = 1 := by simpa only [d369784, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47590 p hg
    simpa only [d369784, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369692 p = 1 := by simpa only [d369784, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47591 p hg
    simpa only [d369784, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47593 (p : Pattern) (guard : d369689 p = 1) : d50561 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369497 p = 1 := by simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47256 p hg
    simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47594 (p : Pattern) (guard : d369690 p = 1) : d50562 p ≤ (1 : Int) + d367794 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369689 p = 1 := by simpa only [d369690, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47593 p hg
    simpa only [d369690, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369690, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46791 p hg
    simpa only [d369690, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47595 (p : Pattern) (guard : d369691 p = 1) : d50562 p ≤ (1 : Int) + d367794 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369690 p = 1 := by simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47594 p hg
    simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369510 p = 1 := by simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47277 p hg
    simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47596 (p : Pattern) (guard : d369692 p = 1) : d50573 p ≤ (1 : Int) + d367802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369691 p = 1 := by simpa only [d369692, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47595 p hg
    simpa only [d369692, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369692, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369692, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47597 (p : Pattern) (guard : d369693 p = 1) : d50574 p ≤ (1 : Int) + d367803 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369692 p = 1 := by simpa only [d369693, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47596 p hg
    simpa only [d369693, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369693, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d369693, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47598 (p : Pattern) (guard : d369785 p = 1) : d50729 p ≤ (1 : Int) + d367913 p := by
  cases selected : p 161 with
  | false =>
    have hg : d369784 p = 1 := by simpa only [d369785, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47592 p hg
    simpa only [d369785, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369693 p = 1 := by simpa only [d369785, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47597 p hg
    simpa only [d369785, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47599 (p : Pattern) (guard : d369786 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369785 p = 1 := by simpa only [d369786, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47598 p hg
    simpa only [d369786, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369786, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46798 p hg
    simpa only [d369786, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47600 (p : Pattern) (guard : d369787 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369786 p = 1 := by simpa only [d369787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47599 p hg
    simpa only [d369787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369583 p = 1 := by simpa only [d369787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47282 p hg
    simpa only [d369787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47601 (p : Pattern) (guard : d369788 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369782 p = 1 := by simpa only [d369788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47586 p hg
    simpa only [d369788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369787 p = 1 := by simpa only [d369788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47600 p hg
    simpa only [d369788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47602 (p : Pattern) (guard : d369789 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369788 p = 1 := by simpa only [d369789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47601 p hg
    simpa only [d369789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369585 p = 1 := by simpa only [d369789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47284 p hg
    simpa only [d369789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47603 (p : Pattern) (guard : d369790 p = 1) : d50734 p ≤ (1 : Int) + d367918 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369790, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46762 p hg
    simpa only [d369790, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369789 p = 1 := by simpa only [d369790, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47602 p hg
    simpa only [d369790, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47604 (p : Pattern) (guard : d369791 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369791, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46761 p hg
    simpa only [d369791, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369790 p = 1 := by simpa only [d369791, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47603 p hg
    simpa only [d369791, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47605 (p : Pattern) (guard : d369792 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369584 p = 1 := by simpa only [d369792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47283 p hg
    simpa only [d369792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d275550 p = 1 := by simpa only [d369792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46801 p hg
    simpa only [d369792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47606 (p : Pattern) (guard : d369793 p = 1) : d50733 p ≤ (1 : Int) + d367917 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369585 p = 1 := by simpa only [d369793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47284 p hg
    simpa only [d369793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369792 p = 1 := by simpa only [d369793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47605 p hg
    simpa only [d369793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47607 (p : Pattern) (guard : d369794 p = 1) : d50734 p ≤ (1 : Int) + d367918 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369794, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46762 p hg
    simpa only [d369794, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369793 p = 1 := by simpa only [d369794, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47606 p hg
    simpa only [d369794, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47608 (p : Pattern) (guard : d369795 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369795, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46761 p hg
    simpa only [d369795, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369794 p = 1 := by simpa only [d369795, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47607 p hg
    simpa only [d369795, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47609 (p : Pattern) (guard : d369796 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369791 p = 1 := by simpa only [d369796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47604 p hg
    simpa only [d369796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369795 p = 1 := by simpa only [d369796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47608 p hg
    simpa only [d369796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47610 (p : Pattern) (guard : d369797 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369796 p = 1 := by simpa only [d369797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47609 p hg
    simpa only [d369797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369589 p = 1 := by simpa only [d369797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47288 p hg
    simpa only [d369797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47611 (p : Pattern) (guard : d369798 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369797 p = 1 := by simpa only [d369798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47610 p hg
    simpa only [d369798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46806 p hg
    simpa only [d369798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47612 (p : Pattern) (guard : d369799 p = 1) : d50737 p ≤ (1 : Int) + d367921 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369798 p = 1 := by simpa only [d369799, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47611 p hg
    simpa only [d369799, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369799, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46810 p hg
    simpa only [d369799, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47613 (p : Pattern) (guard : d369800 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369800, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46646 p hg
    simpa only [d369800, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369799 p = 1 := by simpa only [d369800, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47612 p hg
    simpa only [d369800, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47614 (p : Pattern) (guard : d369801 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369442 p = 1 := by simpa only [d369801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47027 p hg
    simpa only [d369801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46806 p hg
    simpa only [d369801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47615 (p : Pattern) (guard : d369802 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369589 p = 1 := by simpa only [d369802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47288 p hg
    simpa only [d369802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369801 p = 1 := by simpa only [d369802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47614 p hg
    simpa only [d369802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47616 (p : Pattern) (guard : d369803 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369802 p = 1 := by simpa only [d369803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47615 p hg
    simpa only [d369803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46806 p hg
    simpa only [d369803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47617 (p : Pattern) (guard : d369804 p = 1) : d50737 p ≤ (1 : Int) + d367921 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369803 p = 1 := by simpa only [d369804, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47616 p hg
    simpa only [d369804, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369804, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46810 p hg
    simpa only [d369804, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47618 (p : Pattern) (guard : d369805 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369805, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46646 p hg
    simpa only [d369805, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369804 p = 1 := by simpa only [d369805, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47617 p hg
    simpa only [d369805, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47619 (p : Pattern) (guard : d369806 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369800 p = 1 := by simpa only [d369806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47613 p hg
    simpa only [d369806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369805 p = 1 := by simpa only [d369806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47618 p hg
    simpa only [d369806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47620 (p : Pattern) (guard : d369807 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369806 p = 1 := by simpa only [d369807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47619 p hg
    simpa only [d369807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47621 (p : Pattern) (guard : d369808 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369807 p = 1 := by simpa only [d369808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47620 p hg
    simpa only [d369808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47622 (p : Pattern) (guard : d369809 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369808 p = 1 := by simpa only [d369809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47621 p hg
    simpa only [d369809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47623 (p : Pattern) (guard : d369810 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369801 p = 1 := by simpa only [d369810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47614 p hg
    simpa only [d369810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46806 p hg
    simpa only [d369810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47624 (p : Pattern) (guard : d369811 p = 1) : d50735 p ≤ (1 : Int) + d367919 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369810 p = 1 := by simpa only [d369811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47623 p hg
    simpa only [d369811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46806 p hg
    simpa only [d369811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47625 (p : Pattern) (guard : d369812 p = 1) : d50737 p ≤ (1 : Int) + d367921 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369811 p = 1 := by simpa only [d369812, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47624 p hg
    simpa only [d369812, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369812, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46810 p hg
    simpa only [d369812, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47626 (p : Pattern) (guard : d369813 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369813, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46646 p hg
    simpa only [d369813, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369812 p = 1 := by simpa only [d369813, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47625 p hg
    simpa only [d369813, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47627 (p : Pattern) (guard : d369814 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369805 p = 1 := by simpa only [d369814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47618 p hg
    simpa only [d369814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369813 p = 1 := by simpa only [d369814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47626 p hg
    simpa only [d369814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47628 (p : Pattern) (guard : d369815 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369814 p = 1 := by simpa only [d369815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47627 p hg
    simpa only [d369815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47629 (p : Pattern) (guard : d369816 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369815 p = 1 := by simpa only [d369816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47628 p hg
    simpa only [d369816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47630 (p : Pattern) (guard : d369817 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369816 p = 1 := by simpa only [d369817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47629 p hg
    simpa only [d369817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47631 (p : Pattern) (guard : d369818 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369809 p = 1 := by simpa only [d369818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47622 p hg
    simpa only [d369818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369817 p = 1 := by simpa only [d369818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47630 p hg
    simpa only [d369818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47632 (p : Pattern) (guard : d369819 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369818 p = 1 := by simpa only [d369819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47631 p hg
    simpa only [d369819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47633 (p : Pattern) (guard : d369820 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369805 p = 1 := by simpa only [d369820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47618 p hg
    simpa only [d369820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47634 (p : Pattern) (guard : d369821 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369820 p = 1 := by simpa only [d369821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47633 p hg
    simpa only [d369821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47635 (p : Pattern) (guard : d369822 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369821 p = 1 := by simpa only [d369822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47634 p hg
    simpa only [d369822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47636 (p : Pattern) (guard : d369823 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369822 p = 1 := by simpa only [d369823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47635 p hg
    simpa only [d369823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47637 (p : Pattern) (guard : d369824 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369823 p = 1 := by simpa only [d369824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47636 p hg
    simpa only [d369824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47638 (p : Pattern) (guard : d369825 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 90 with
  | false =>
    have hg : d369824 p = 1 := by simpa only [d369825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47637 p hg
    simpa only [d369825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47639 (p : Pattern) (guard : d369826 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369819 p = 1 := by simpa only [d369826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47632 p hg
    simpa only [d369826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369825 p = 1 := by simpa only [d369826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47638 p hg
    simpa only [d369826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47640 (p : Pattern) (guard : d369827 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369826 p = 1 := by simpa only [d369827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47639 p hg
    simpa only [d369827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47641 (p : Pattern) (guard : d369828 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369827 p = 1 := by simpa only [d369828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47640 p hg
    simpa only [d369828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47642 (p : Pattern) (guard : d369829 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369829, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369829, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369828 p = 1 := by simpa only [d369829, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47641 p hg
    simpa only [d369829, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47643 (p : Pattern) (guard : d369830 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46759 p hg
    simpa only [d369830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369829 p = 1 := by simpa only [d369830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47642 p hg
    simpa only [d369830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47644 (p : Pattern) (guard : d369831 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369813 p = 1 := by simpa only [d369831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47626 p hg
    simpa only [d369831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47645 (p : Pattern) (guard : d369832 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369831 p = 1 := by simpa only [d369832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47644 p hg
    simpa only [d369832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47646 (p : Pattern) (guard : d369833 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369832 p = 1 := by simpa only [d369833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47645 p hg
    simpa only [d369833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47647 (p : Pattern) (guard : d369834 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369833 p = 1 := by simpa only [d369834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47646 p hg
    simpa only [d369834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47648 (p : Pattern) (guard : d369835 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369834 p = 1 := by simpa only [d369835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47647 p hg
    simpa only [d369835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47649 (p : Pattern) (guard : d369836 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369835 p = 1 := by simpa only [d369836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47648 p hg
    simpa only [d369836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47650 (p : Pattern) (guard : d369837 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369836 p = 1 := by simpa only [d369837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47649 p hg
    simpa only [d369837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47651 (p : Pattern) (guard : d369838 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369837 p = 1 := by simpa only [d369838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47650 p hg
    simpa only [d369838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47652 (p : Pattern) (guard : d369839 p = 1) : d50738 p ≤ (1 : Int) + d367922 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46760 p hg
    simpa only [d369839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369838 p = 1 := by simpa only [d369839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47651 p hg
    simpa only [d369839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47653 (p : Pattern) (guard : d369840 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369840, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369840, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369839 p = 1 := by simpa only [d369840, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47652 p hg
    simpa only [d369840, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47654 (p : Pattern) (guard : d369841 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46759 p hg
    simpa only [d369841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369840 p = 1 := by simpa only [d369841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47653 p hg
    simpa only [d369841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47655 (p : Pattern) (guard : d369842 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 69 with
  | false =>
    have hg : d369830 p = 1 := by simpa only [d369842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47643 p hg
    simpa only [d369842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369841 p = 1 := by simpa only [d369842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47654 p hg
    simpa only [d369842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47656 (p : Pattern) (guard : d369843 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 51 with
  | false =>
    have hg : d369842 p = 1 := by simpa only [d369843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47655 p hg
    simpa only [d369843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46759 p hg
    simpa only [d369843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47657 (p : Pattern) (guard : d369844 p = 1) : d50739 p ≤ (1 : Int) + d367923 p := by
  cases selected : p 50 with
  | false =>
    have hg : d369843 p = 1 := by simpa only [d369844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47656 p hg
    simpa only [d369844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46759 p hg
    simpa only [d369844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47658 (p : Pattern) (guard : d369845 p = 1) : d50822 p ≤ (1 : Int) + d367984 p := by
  cases selected : p 49 with
  | false =>
    have hg : d369844 p = 1 := by simpa only [d369845, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47657 p hg
    simpa only [d369845, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369845, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46827 p hg
    simpa only [d369845, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47659 (p : Pattern) (guard : d369846 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 48 with
  | false =>
    have hg : d369773 p = 1 := by simpa only [d369846, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47555 p hg
    simpa only [d369846, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369845 p = 1 := by simpa only [d369846, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47658 p hg
    simpa only [d369846, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47660 (p : Pattern) (guard : d369847 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d369847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369846 p = 1 := by simpa only [d369847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47659 p hg
    simpa only [d369847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47661 (p : Pattern) (guard : d369848 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d369848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369847 p = 1 := by simpa only [d369848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47660 p hg
    simpa only [d369848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47662 (p : Pattern) (guard : d369849 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d369849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369848 p = 1 := by simpa only [d369849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47661 p hg
    simpa only [d369849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47663 (p : Pattern) (guard : d369850 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d369850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369849 p = 1 := by simpa only [d369850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47662 p hg
    simpa only [d369850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47664 (p : Pattern) (guard : d369851 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d369851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369850 p = 1 := by simpa only [d369851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47663 p hg
    simpa only [d369851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47665 (p : Pattern) (guard : d369852 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d369852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369851 p = 1 := by simpa only [d369852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47664 p hg
    simpa only [d369852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47666 (p : Pattern) (guard : d369853 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46644 p hg
    simpa only [d369853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369852 p = 1 := by simpa only [d369853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47665 p hg
    simpa only [d369853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47667 (p : Pattern) (guard : d369854 p = 1) : d50823 p ≤ (1 : Int) + d367985 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d369622 p = 1 := by simpa only [d369854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47327 p hg
    simpa only [d369854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369853 p = 1 := by simpa only [d369854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47666 p hg
    simpa only [d369854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47668 (p : Pattern) (guard : d369855 p = 1) : d50553 p ≤ (1 : Int) + d367764 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369389 p = 1 := by simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46880 p hg
    simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46662 p hg
    simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47669 (p : Pattern) (guard : d369856 p = 1) : d50570 p ≤ (1 : Int) + d367784 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369855 p = 1 := by simpa only [d369856, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47668 p hg
    simpa only [d369856, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369856, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46664 p hg
    simpa only [d369856, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47670 (p : Pattern) (guard : d369857 p = 1) : d50571 p ≤ (1 : Int) + d367785 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369856 p = 1 := by simpa only [d369857, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47669 p hg
    simpa only [d369857, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369857, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46666 p hg
    simpa only [d369857, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47671 (p : Pattern) (guard : d369858 p = 1) : d50572 p ≤ (1 : Int) + d367801 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369858, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46649 p hg
    simpa only [d369858, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369857 p = 1 := by simpa only [d369858, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47670 p hg
    simpa only [d369858, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47672 (p : Pattern) (guard : d369859 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369858 p = 1 := by simpa only [d369859, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47671 p hg
    simpa only [d369859, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369859, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46669 p hg
    simpa only [d369859, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47673 (p : Pattern) (guard : d369860 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369695 p = 1 := by simpa only [d369860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47404 p hg
    simpa only [d369860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369859 p = 1 := by simpa only [d369860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47672 p hg
    simpa only [d369860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47674 (p : Pattern) (guard : d369861 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369688 p = 1 := by simpa only [d369861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47397 p hg
    simpa only [d369861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369860 p = 1 := by simpa only [d369861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47673 p hg
    simpa only [d369861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47675 (p : Pattern) (guard : d369862 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369507 p = 1 := by simpa only [d369862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47103 p hg
    simpa only [d369862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369859 p = 1 := by simpa only [d369862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47672 p hg
    simpa only [d369862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47676 (p : Pattern) (guard : d369863 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369859 p = 1 := by simpa only [d369863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47672 p hg
    simpa only [d369863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46671 p hg
    simpa only [d369863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47677 (p : Pattern) (guard : d369864 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369862 p = 1 := by simpa only [d369864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47675 p hg
    simpa only [d369864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369863 p = 1 := by simpa only [d369864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47676 p hg
    simpa only [d369864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47678 (p : Pattern) (guard : d369865 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369861 p = 1 := by simpa only [d369865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47674 p hg
    simpa only [d369865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369864 p = 1 := by simpa only [d369865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47677 p hg
    simpa only [d369865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47679 (p : Pattern) (guard : d369866 p = 1) : d50577 p ≤ (1 : Int) + d367806 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369866, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46648 p hg
    simpa only [d369866, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369865 p = 1 := by simpa only [d369866, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47678 p hg
    simpa only [d369866, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47680 (p : Pattern) (guard : d369867 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369867, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46647 p hg
    simpa only [d369867, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369866 p = 1 := by simpa only [d369867, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47679 p hg
    simpa only [d369867, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47681 (p : Pattern) (guard : d369868 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369863 p = 1 := by simpa only [d369868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47676 p hg
    simpa only [d369868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46671 p hg
    simpa only [d369868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47682 (p : Pattern) (guard : d369869 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369864 p = 1 := by simpa only [d369869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47677 p hg
    simpa only [d369869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369868 p = 1 := by simpa only [d369869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47681 p hg
    simpa only [d369869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47683 (p : Pattern) (guard : d369870 p = 1) : d50577 p ≤ (1 : Int) + d367806 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369870, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46648 p hg
    simpa only [d369870, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369869 p = 1 := by simpa only [d369870, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47682 p hg
    simpa only [d369870, d50577, d367806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47684 (p : Pattern) (guard : d369871 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369871, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46647 p hg
    simpa only [d369871, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369870 p = 1 := by simpa only [d369871, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47683 p hg
    simpa only [d369871, d50578, d367807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47685 (p : Pattern) (guard : d369872 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369867 p = 1 := by simpa only [d369872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47680 p hg
    simpa only [d369872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369871 p = 1 := by simpa only [d369872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47684 p hg
    simpa only [d369872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47686 (p : Pattern) (guard : d369873 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369871 p = 1 := by simpa only [d369873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47684 p hg
    simpa only [d369873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46677 p hg
    simpa only [d369873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47687 (p : Pattern) (guard : d369874 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369872 p = 1 := by simpa only [d369874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47685 p hg
    simpa only [d369874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369873 p = 1 := by simpa only [d369874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47686 p hg
    simpa only [d369874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47688 (p : Pattern) (guard : d369875 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369874 p = 1 := by simpa only [d369875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47687 p hg
    simpa only [d369875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46677 p hg
    simpa only [d369875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47689 (p : Pattern) (guard : d369876 p = 1) : d50590 p ≤ (1 : Int) + d367819 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369875 p = 1 := by simpa only [d369876, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47688 p hg
    simpa only [d369876, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369876, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46681 p hg
    simpa only [d369876, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47690 (p : Pattern) (guard : d369877 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369877, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46646 p hg
    simpa only [d369877, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369876 p = 1 := by simpa only [d369877, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47689 p hg
    simpa only [d369877, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47691 (p : Pattern) (guard : d369878 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369873 p = 1 := by simpa only [d369878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47686 p hg
    simpa only [d369878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46677 p hg
    simpa only [d369878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47692 (p : Pattern) (guard : d369879 p = 1) : d50578 p ≤ (1 : Int) + d367807 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369878 p = 1 := by simpa only [d369879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47691 p hg
    simpa only [d369879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46677 p hg
    simpa only [d369879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47693 (p : Pattern) (guard : d369880 p = 1) : d50590 p ≤ (1 : Int) + d367819 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369879 p = 1 := by simpa only [d369880, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47692 p hg
    simpa only [d369880, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369880, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46681 p hg
    simpa only [d369880, d50590, d367819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47694 (p : Pattern) (guard : d369881 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369881, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46646 p hg
    simpa only [d369881, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369880 p = 1 := by simpa only [d369881, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47693 p hg
    simpa only [d369881, d50591, d367820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47695 (p : Pattern) (guard : d369882 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369877 p = 1 := by simpa only [d369882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47690 p hg
    simpa only [d369882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369881 p = 1 := by simpa only [d369882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47694 p hg
    simpa only [d369882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47696 (p : Pattern) (guard : d369883 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369882 p = 1 := by simpa only [d369883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47695 p hg
    simpa only [d369883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47697 (p : Pattern) (guard : d369884 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369883 p = 1 := by simpa only [d369884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47696 p hg
    simpa only [d369884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47698 (p : Pattern) (guard : d369885 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369884 p = 1 := by simpa only [d369885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47697 p hg
    simpa only [d369885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47699 (p : Pattern) (guard : d369886 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369881 p = 1 := by simpa only [d369886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47694 p hg
    simpa only [d369886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47700 (p : Pattern) (guard : d369887 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369886 p = 1 := by simpa only [d369887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47699 p hg
    simpa only [d369887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47701 (p : Pattern) (guard : d369888 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369887 p = 1 := by simpa only [d369888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47700 p hg
    simpa only [d369888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47702 (p : Pattern) (guard : d369889 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369888 p = 1 := by simpa only [d369889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47701 p hg
    simpa only [d369889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47703 (p : Pattern) (guard : d369890 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369885 p = 1 := by simpa only [d369890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47698 p hg
    simpa only [d369890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369889 p = 1 := by simpa only [d369890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47702 p hg
    simpa only [d369890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47704 (p : Pattern) (guard : d369891 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369890 p = 1 := by simpa only [d369891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47703 p hg
    simpa only [d369891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47705 (p : Pattern) (guard : d369892 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369891 p = 1 := by simpa only [d369892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47704 p hg
    simpa only [d369892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47706 (p : Pattern) (guard : d369893 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369892 p = 1 := by simpa only [d369893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47705 p hg
    simpa only [d369893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47707 (p : Pattern) (guard : d369894 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369893 p = 1 := by simpa only [d369894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47706 p hg
    simpa only [d369894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47708 (p : Pattern) (guard : d369895 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369894 p = 1 := by simpa only [d369895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47707 p hg
    simpa only [d369895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47709 (p : Pattern) (guard : d369896 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369895 p = 1 := by simpa only [d369896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47708 p hg
    simpa only [d369896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47710 (p : Pattern) (guard : d369897 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 69 with
  | false =>
    have hg : d369896 p = 1 := by simpa only [d369897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47709 p hg
    simpa only [d369897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47711 (p : Pattern) (guard : d369898 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369884 p = 1 := by simpa only [d369898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47697 p hg
    simpa only [d369898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47712 (p : Pattern) (guard : d369899 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369888 p = 1 := by simpa only [d369899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47701 p hg
    simpa only [d369899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47713 (p : Pattern) (guard : d369900 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369898 p = 1 := by simpa only [d369900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47711 p hg
    simpa only [d369900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369899 p = 1 := by simpa only [d369900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47712 p hg
    simpa only [d369900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47714 (p : Pattern) (guard : d369901 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369900 p = 1 := by simpa only [d369901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47713 p hg
    simpa only [d369901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47715 (p : Pattern) (guard : d369902 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369901 p = 1 := by simpa only [d369902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47714 p hg
    simpa only [d369902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47716 (p : Pattern) (guard : d369903 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369902 p = 1 := by simpa only [d369903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47715 p hg
    simpa only [d369903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47717 (p : Pattern) (guard : d369904 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369903 p = 1 := by simpa only [d369904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47716 p hg
    simpa only [d369904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47718 (p : Pattern) (guard : d369905 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 71 with
  | false =>
    have hg : d369894 p = 1 := by simpa only [d369905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47707 p hg
    simpa only [d369905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369904 p = 1 := by simpa only [d369905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47717 p hg
    simpa only [d369905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47719 (p : Pattern) (guard : d369906 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 70 with
  | false =>
    have hg : d369895 p = 1 := by simpa only [d369906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47708 p hg
    simpa only [d369906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369905 p = 1 := by simpa only [d369906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47718 p hg
    simpa only [d369906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47720 (p : Pattern) (guard : d369907 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 69 with
  | false =>
    have hg : d369906 p = 1 := by simpa only [d369907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47719 p hg
    simpa only [d369907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47721 (p : Pattern) (guard : d369908 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 51 with
  | false =>
    have hg : d369897 p = 1 := by simpa only [d369908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47710 p hg
    simpa only [d369908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369907 p = 1 := by simpa only [d369908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47720 p hg
    simpa only [d369908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47722 (p : Pattern) (guard : d369909 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369883 p = 1 := by simpa only [d369909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47696 p hg
    simpa only [d369909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47723 (p : Pattern) (guard : d369910 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369909 p = 1 := by simpa only [d369910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47722 p hg
    simpa only [d369910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47724 (p : Pattern) (guard : d369911 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369887 p = 1 := by simpa only [d369911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47700 p hg
    simpa only [d369911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47725 (p : Pattern) (guard : d369912 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369911 p = 1 := by simpa only [d369912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47724 p hg
    simpa only [d369912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47726 (p : Pattern) (guard : d369913 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369910 p = 1 := by simpa only [d369913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47723 p hg
    simpa only [d369913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369912 p = 1 := by simpa only [d369913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47725 p hg
    simpa only [d369913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47727 (p : Pattern) (guard : d369914 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369913 p = 1 := by simpa only [d369914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47726 p hg
    simpa only [d369914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47728 (p : Pattern) (guard : d369915 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369914 p = 1 := by simpa only [d369915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47727 p hg
    simpa only [d369915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47729 (p : Pattern) (guard : d369916 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369915 p = 1 := by simpa only [d369916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47728 p hg
    simpa only [d369916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47730 (p : Pattern) (guard : d369917 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369882 p = 1 := by simpa only [d369917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47695 p hg
    simpa only [d369917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47731 (p : Pattern) (guard : d369918 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369917 p = 1 := by simpa only [d369918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47730 p hg
    simpa only [d369918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47732 (p : Pattern) (guard : d369919 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369918 p = 1 := by simpa only [d369919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47731 p hg
    simpa only [d369919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47733 (p : Pattern) (guard : d369920 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369886 p = 1 := by simpa only [d369920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47699 p hg
    simpa only [d369920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47734 (p : Pattern) (guard : d369921 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369920 p = 1 := by simpa only [d369921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47733 p hg
    simpa only [d369921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47735 (p : Pattern) (guard : d369922 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369921 p = 1 := by simpa only [d369922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47734 p hg
    simpa only [d369922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47736 (p : Pattern) (guard : d369923 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369919 p = 1 := by simpa only [d369923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47732 p hg
    simpa only [d369923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369922 p = 1 := by simpa only [d369923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47735 p hg
    simpa only [d369923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47737 (p : Pattern) (guard : d369924 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369923 p = 1 := by simpa only [d369924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47736 p hg
    simpa only [d369924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47738 (p : Pattern) (guard : d369925 p = 1) : d50591 p ≤ (1 : Int) + d367820 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369924 p = 1 := by simpa only [d369925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47737 p hg
    simpa only [d369925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46645 p hg
    simpa only [d369925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47739 (p : Pattern) (guard : d369926 p = 1) : d50553 p ≤ (1 : Int) + d367764 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46662 p hg
    simpa only [d369926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46055 p = 1 := by simpa only [d369926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47383 p hg
    simpa only [d369926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47740 (p : Pattern) (guard : d369927 p = 1) : d50570 p ≤ (1 : Int) + d367784 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369926 p = 1 := by simpa only [d369927, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47739 p hg
    simpa only [d369927, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369927, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46664 p hg
    simpa only [d369927, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47741 (p : Pattern) (guard : d369928 p = 1) : d50571 p ≤ (1 : Int) + d367785 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369927 p = 1 := by simpa only [d369928, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47740 p hg
    simpa only [d369928, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369928, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46666 p hg
    simpa only [d369928, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47742 (p : Pattern) (guard : d369929 p = 1) : d50572 p ≤ (1 : Int) + d367801 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369929, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46649 p hg
    simpa only [d369929, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369928 p = 1 := by simpa only [d369929, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47741 p hg
    simpa only [d369929, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47743 (p : Pattern) (guard : d369930 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369929 p = 1 := by simpa only [d369930, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47742 p hg
    simpa only [d369930, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369930, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46669 p hg
    simpa only [d369930, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47744 (p : Pattern) (guard : d369931 p = 1) : d50553 p ≤ (1 : Int) + d367764 p := by
  cases selected : p 180 with
  | false =>
    have hg : d46055 p = 1 := by simpa only [d369931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47383 p hg
    simpa only [d369931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369690 p = 1 := by simpa only [d369931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47399 p hg
    simpa only [d369931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47745 (p : Pattern) (guard : d369932 p = 1) : d50570 p ≤ (1 : Int) + d367784 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369931 p = 1 := by simpa only [d369932, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47744 p hg
    simpa only [d369932, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369932, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46664 p hg
    simpa only [d369932, d50570, d367784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47746 (p : Pattern) (guard : d369933 p = 1) : d50571 p ≤ (1 : Int) + d367785 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369932 p = 1 := by simpa only [d369933, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47745 p hg
    simpa only [d369933, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369933, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46666 p hg
    simpa only [d369933, d50571, d367785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47747 (p : Pattern) (guard : d369934 p = 1) : d50572 p ≤ (1 : Int) + d367801 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369934, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46649 p hg
    simpa only [d369934, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369933 p = 1 := by simpa only [d369934, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47746 p hg
    simpa only [d369934, d50572, d367801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47748 (p : Pattern) (guard : d369935 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369934 p = 1 := by simpa only [d369935, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47747 p hg
    simpa only [d369935, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369935, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46669 p hg
    simpa only [d369935, d50576, d367805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47749 (p : Pattern) (guard : d369936 p = 1) : d50576 p ≤ (1 : Int) + d367805 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369930 p = 1 := by simpa only [d369936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47743 p hg
    simpa only [d369936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369935 p = 1 := by simpa only [d369936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47748 p hg
    simpa only [d369936, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
