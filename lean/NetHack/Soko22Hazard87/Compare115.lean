import NetHack.Soko22Hazard87.Compare114
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare28750 (p : Pattern) (guard : d15563 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2071 p = 1 := by simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28749 p hg
    simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15557 p = 1 := by simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28735 p hg
    simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28751 (p : Pattern) (guard : d17169 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28708 p hg
    simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15563 p = 1 := by simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28750 p hg
    simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28752 (p : Pattern) (guard : d19555 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d17169 p = 1 := by simpa only [d19555, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28751 p hg
    simpa only [d19555, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19555, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d19555, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28753 (p : Pattern) (guard : d19556 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19556, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d19556, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19555 p = 1 := by simpa only [d19556, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28752 p hg
    simpa only [d19556, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28754 (p : Pattern) (guard : d19557 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d19556 p = 1 := by simpa only [d19557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28753 p hg
    simpa only [d19557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d19557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28755 (p : Pattern) (guard : d132514 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d19529 p = 1 := by simpa only [d132514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28740 p hg
    simpa only [d132514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19557 p = 1 := by simpa only [d132514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28754 p hg
    simpa only [d132514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28756 (p : Pattern) (guard : d188413 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17173 p = 1 := by simpa only [d188413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28612 p hg
    simpa only [d188413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d132514 p = 1 := by simpa only [d188413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28755 p hg
    simpa only [d188413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28757 (p : Pattern) (guard : d188414 p = 1) : d48705 p ≤ (-2 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d188413 p = 1 := by simpa only [d188414, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28756 p hg
    simpa only [d188414, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188414, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27470 p hg
    simpa only [d188414, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28758 (p : Pattern) (guard : d188415 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188415, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27404 p hg
    simpa only [d188415, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188414 p = 1 := by simpa only [d188415, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28757 p hg
    simpa only [d188415, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28759 (p : Pattern) (guard : d17177 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17172 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28611 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28760 (p : Pattern) (guard : d19558 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d19557 p = 1 := by simpa only [d19558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28754 p hg
    simpa only [d19558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d19558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28761 (p : Pattern) (guard : d188197 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17177 p = 1 := by simpa only [d188197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28759 p hg
    simpa only [d188197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19558 p = 1 := by simpa only [d188197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28760 p hg
    simpa only [d188197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28762 (p : Pattern) (guard : d188198 p = 1) : d48705 p ≤ (-2 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d188197 p = 1 := by simpa only [d188198, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28761 p hg
    simpa only [d188198, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188198, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27470 p hg
    simpa only [d188198, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28763 (p : Pattern) (guard : d188199 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188199, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27404 p hg
    simpa only [d188199, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188198 p = 1 := by simpa only [d188199, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28762 p hg
    simpa only [d188199, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28764 (p : Pattern) (guard : d188416 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d188415 p = 1 := by simpa only [d188416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28758 p hg
    simpa only [d188416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188199 p = 1 := by simpa only [d188416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28763 p hg
    simpa only [d188416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28765 (p : Pattern) (guard : d188417 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d188416 p = 1 := by simpa only [d188417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28764 p hg
    simpa only [d188417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28766 (p : Pattern) (guard : d188418 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d188417 p = 1 := by simpa only [d188418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28765 p hg
    simpa only [d188418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28767 (p : Pattern) (guard : d188419 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d188418 p = 1 := by simpa only [d188419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28766 p hg
    simpa only [d188419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28768 (p : Pattern) (guard : d188220 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d188199 p = 1 := by simpa only [d188220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28763 p hg
    simpa only [d188220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28769 (p : Pattern) (guard : d188221 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d188220 p = 1 := by simpa only [d188221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28768 p hg
    simpa only [d188221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28770 (p : Pattern) (guard : d188222 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d188221 p = 1 := by simpa only [d188222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28769 p hg
    simpa only [d188222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28771 (p : Pattern) (guard : d188223 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d188222 p = 1 := by simpa only [d188223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28770 p hg
    simpa only [d188223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28772 (p : Pattern) (guard : d188420 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d188419 p = 1 := by simpa only [d188420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28767 p hg
    simpa only [d188420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188223 p = 1 := by simpa only [d188420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28771 p hg
    simpa only [d188420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28773 (p : Pattern) (guard : d188421 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188420 p = 1 := by simpa only [d188421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28772 p hg
    simpa only [d188421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28774 (p : Pattern) (guard : d188422 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 89 with
  | false =>
    have hg : d188421 p = 1 := by simpa only [d188422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28773 p hg
    simpa only [d188422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28775 (p : Pattern) (guard : d188423 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188422 p = 1 := by simpa only [d188423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28774 p hg
    simpa only [d188423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28776 (p : Pattern) (guard : d188424 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188423 p = 1 := by simpa only [d188424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28775 p hg
    simpa only [d188424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28777 (p : Pattern) (guard : d188425 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188425, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27402 p hg
    simpa only [d188425, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188424 p = 1 := by simpa only [d188425, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28776 p hg
    simpa only [d188425, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28778 (p : Pattern) (guard : d188426 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188425 p = 1 := by simpa only [d188426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28777 p hg
    simpa only [d188426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28779 (p : Pattern) (guard : d188427 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 69 with
  | false =>
    have hg : d188426 p = 1 := by simpa only [d188427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28778 p hg
    simpa only [d188427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28780 (p : Pattern) (guard : d188428 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 51 with
  | false =>
    have hg : d188427 p = 1 := by simpa only [d188428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28779 p hg
    simpa only [d188428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28781 (p : Pattern) (guard : d188429 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 50 with
  | false =>
    have hg : d188428 p = 1 := by simpa only [d188429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28780 p hg
    simpa only [d188429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28782 (p : Pattern) (guard : d188430 p = 1) : d48748 p ≤ (-2 : Int) + d188517 p := by
  cases selected : p 49 with
  | false =>
    have hg : d188429 p = 1 := by simpa only [d188430, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28781 p hg
    simpa only [d188430, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188430, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27487 p hg
    simpa only [d188430, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28783 (p : Pattern) (guard : d188431 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188431, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27400 p hg
    simpa only [d188431, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188430 p = 1 := by simpa only [d188431, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28782 p hg
    simpa only [d188431, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28784 (p : Pattern) (guard : d188432 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188431 p = 1 := by simpa only [d188432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28783 p hg
    simpa only [d188432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28785 (p : Pattern) (guard : d188433 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188432 p = 1 := by simpa only [d188433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28784 p hg
    simpa only [d188433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28786 (p : Pattern) (guard : d188434 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188433 p = 1 := by simpa only [d188434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28785 p hg
    simpa only [d188434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28787 (p : Pattern) (guard : d188435 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188434 p = 1 := by simpa only [d188435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28786 p hg
    simpa only [d188435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28788 (p : Pattern) (guard : d188436 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188435 p = 1 := by simpa only [d188436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28787 p hg
    simpa only [d188436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28789 (p : Pattern) (guard : d188437 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188436 p = 1 := by simpa only [d188437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28788 p hg
    simpa only [d188437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28790 (p : Pattern) (guard : d188438 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188437 p = 1 := by simpa only [d188438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28789 p hg
    simpa only [d188438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28791 (p : Pattern) (guard : d188439 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188438 p = 1 := by simpa only [d188439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28790 p hg
    simpa only [d188439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28792 (p : Pattern) (guard : d188440 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188439 p = 1 := by simpa only [d188440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28791 p hg
    simpa only [d188440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28793 (p : Pattern) (guard : d188441 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188440 p = 1 := by simpa only [d188441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28792 p hg
    simpa only [d188441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28794 (p : Pattern) (guard : d188442 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d188412 p = 1 := by simpa only [d188442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28469 p hg
    simpa only [d188442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188441 p = 1 := by simpa only [d188442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28793 p hg
    simpa only [d188442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28795 (p : Pattern) (guard : d188443 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 260 with
  | false =>
    have hg : d188442 p = 1 := by simpa only [d188443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28794 p hg
    simpa only [d188443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28796 (p : Pattern) (guard : d188444 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 259 with
  | false =>
    have hg : d188443 p = 1 := by simpa only [d188444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28795 p hg
    simpa only [d188444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28797 (p : Pattern) (guard : d188445 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 258 with
  | false =>
    have hg : d188444 p = 1 := by simpa only [d188445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28796 p hg
    simpa only [d188445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28798 (p : Pattern) (guard : d188446 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 257 with
  | false =>
    have hg : d188445 p = 1 := by simpa only [d188446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28797 p hg
    simpa only [d188446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28799 (p : Pattern) (guard : d188447 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 256 with
  | false =>
    have hg : d188446 p = 1 := by simpa only [d188447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28798 p hg
    simpa only [d188447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28800 (p : Pattern) (guard : d188448 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 255 with
  | false =>
    have hg : d188447 p = 1 := by simpa only [d188448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28799 p hg
    simpa only [d188448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28801 (p : Pattern) (guard : d188449 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 254 with
  | false =>
    have hg : d188448 p = 1 := by simpa only [d188449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28800 p hg
    simpa only [d188449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28802 (p : Pattern) (guard : d188450 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 253 with
  | false =>
    have hg : d188449 p = 1 := by simpa only [d188450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28801 p hg
    simpa only [d188450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28803 (p : Pattern) (guard : d188451 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 252 with
  | false =>
    have hg : d188450 p = 1 := by simpa only [d188451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28802 p hg
    simpa only [d188451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28804 (p : Pattern) (guard : d188452 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 251 with
  | false =>
    have hg : d188451 p = 1 := by simpa only [d188452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28803 p hg
    simpa only [d188452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28805 (p : Pattern) (guard : d188453 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 250 with
  | false =>
    have hg : d188452 p = 1 := by simpa only [d188453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28804 p hg
    simpa only [d188453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28806 (p : Pattern) (guard : d188454 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 249 with
  | false =>
    have hg : d188453 p = 1 := by simpa only [d188454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28805 p hg
    simpa only [d188454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28807 (p : Pattern) (guard : d188455 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 245 with
  | false =>
    have hg : d188454 p = 1 := by simpa only [d188455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28806 p hg
    simpa only [d188455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28808 (p : Pattern) (guard : d188456 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 200 with
  | false =>
    have hg : d188455 p = 1 := by simpa only [d188456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28807 p hg
    simpa only [d188456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28809 (p : Pattern) (guard : d188457 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 199 with
  | false =>
    have hg : d188456 p = 1 := by simpa only [d188457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28808 p hg
    simpa only [d188457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28810 (p : Pattern) (guard : d188458 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 186 with
  | false =>
    have hg : d188457 p = 1 := by simpa only [d188458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28809 p hg
    simpa only [d188458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28811 (p : Pattern) (guard : d188459 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 185 with
  | false =>
    have hg : d188458 p = 1 := by simpa only [d188459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28810 p hg
    simpa only [d188459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28812 (p : Pattern) (guard : d188460 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 184 with
  | false =>
    have hg : d188459 p = 1 := by simpa only [d188460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28811 p hg
    simpa only [d188460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28813 (p : Pattern) (guard : d188461 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 181 with
  | false =>
    have hg : d188460 p = 1 := by simpa only [d188461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28812 p hg
    simpa only [d188461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28814 (p : Pattern) (guard : d188462 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 177 with
  | false =>
    have hg : d188461 p = 1 := by simpa only [d188462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28813 p hg
    simpa only [d188462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28815 (p : Pattern) (guard : d188463 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 164 with
  | false =>
    have hg : d188462 p = 1 := by simpa only [d188463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28814 p hg
    simpa only [d188463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28816 (p : Pattern) (guard : d188464 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 156 with
  | false =>
    have hg : d188463 p = 1 := by simpa only [d188464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28815 p hg
    simpa only [d188464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28817 (p : Pattern) (guard : d188465 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 155 with
  | false =>
    have hg : d188464 p = 1 := by simpa only [d188465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28816 p hg
    simpa only [d188465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28818 (p : Pattern) (guard : d188466 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 134 with
  | false =>
    have hg : d188465 p = 1 := by simpa only [d188466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28817 p hg
    simpa only [d188466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28819 (p : Pattern) (guard : d188467 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 133 with
  | false =>
    have hg : d188466 p = 1 := by simpa only [d188467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28818 p hg
    simpa only [d188467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28820 (p : Pattern) (guard : d188468 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 120 with
  | false =>
    have hg : d188467 p = 1 := by simpa only [d188468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28819 p hg
    simpa only [d188468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28821 (p : Pattern) (guard : d188469 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 118 with
  | false =>
    have hg : d188468 p = 1 := by simpa only [d188469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28820 p hg
    simpa only [d188469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28822 (p : Pattern) (guard : d188470 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 114 with
  | false =>
    have hg : d188469 p = 1 := by simpa only [d188470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28821 p hg
    simpa only [d188470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28823 (p : Pattern) (guard : d188471 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 111 with
  | false =>
    have hg : d188470 p = 1 := by simpa only [d188471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28822 p hg
    simpa only [d188471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28824 (p : Pattern) (guard : d188472 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 98 with
  | false =>
    have hg : d188471 p = 1 := by simpa only [d188472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28823 p hg
    simpa only [d188472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28825 (p : Pattern) (guard : d188473 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 97 with
  | false =>
    have hg : d188472 p = 1 := by simpa only [d188473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28824 p hg
    simpa only [d188473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28826 (p : Pattern) (guard : d188474 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 94 with
  | false =>
    have hg : d188473 p = 1 := by simpa only [d188474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28825 p hg
    simpa only [d188474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28827 (p : Pattern) (guard : d188475 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 76 with
  | false =>
    have hg : d188474 p = 1 := by simpa only [d188475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28826 p hg
    simpa only [d188475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28828 (p : Pattern) (guard : d188476 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 67 with
  | false =>
    have hg : d188475 p = 1 := by simpa only [d188476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28827 p hg
    simpa only [d188476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28829 (p : Pattern) (guard : d188477 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 52 with
  | false =>
    have hg : d188476 p = 1 := by simpa only [d188477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28828 p hg
    simpa only [d188477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28830 (p : Pattern) (guard : d188478 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 47 with
  | false =>
    have hg : d188477 p = 1 := by simpa only [d188478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28829 p hg
    simpa only [d188478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28831 (p : Pattern) (guard : d188479 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 46 with
  | false =>
    have hg : d188478 p = 1 := by simpa only [d188479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28830 p hg
    simpa only [d188479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28832 (p : Pattern) (guard : d188480 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 45 with
  | false =>
    have hg : d188479 p = 1 := by simpa only [d188480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28831 p hg
    simpa only [d188480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28833 (p : Pattern) (guard : d188481 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 30 with
  | false =>
    have hg : d188480 p = 1 := by simpa only [d188481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28832 p hg
    simpa only [d188481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28834 (p : Pattern) (guard : d188482 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 29 with
  | false =>
    have hg : d188481 p = 1 := by simpa only [d188482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28833 p hg
    simpa only [d188482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28835 (p : Pattern) (guard : d188483 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 28 with
  | false =>
    have hg : d188482 p = 1 := by simpa only [d188483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28834 p hg
    simpa only [d188483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28836 (p : Pattern) (guard : d188484 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 27 with
  | false =>
    have hg : d188483 p = 1 := by simpa only [d188484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28835 p hg
    simpa only [d188484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28837 (p : Pattern) (guard : d188485 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 25 with
  | false =>
    have hg : d188484 p = 1 := by simpa only [d188485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28836 p hg
    simpa only [d188485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28838 (p : Pattern) (guard : d0 p = 1) : d48749 p ≤ (-1 : Int) + d48308 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28839 (p : Pattern) (guard : d0 p = 1) : d48749 p ≤ (-2 : Int) + d48308 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28840 (p : Pattern) (guard : d0 p = 1) : d48997 p ≤ (-1 : Int) + d48308 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28841 (p : Pattern) (guard : d0 p = 1) : d48997 p ≤ (-2 : Int) + d48308 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28842 (p : Pattern) (guard : d0 p = 1) : d48997 p ≤ (1 : Int) + d188744 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28843 (p : Pattern) (guard : d0 p = 1) : d48997 p ≤ (0 : Int) + d188744 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28844 (p : Pattern) (guard : d0 p = 1) : d48997 p ≤ (-1 : Int) + d49102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28845 (p : Pattern) (guard : d0 p = 1) : d48997 p ≤ (-2 : Int) + d49102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28846 (p : Pattern) (guard : d0 p = 1) : d48997 p ≤ (-1 : Int) + d48749 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28847 (p : Pattern) (guard : d0 p = 1) : d48997 p ≤ (-2 : Int) + d48749 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28848 (p : Pattern) (guard : d0 p = 1) : d48997 p ≤ (-1 : Int) + d190630 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28849 (p : Pattern) (guard : d0 p = 1) : d48997 p ≤ (-2 : Int) + d190630 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28850 (p : Pattern) (guard : d0 p = 1) : d49102 p ≤ (-1 : Int) + d49102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28851 (p : Pattern) (guard : d0 p = 1) : d49102 p ≤ (-2 : Int) + d49102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28852 (p : Pattern) (guard : d0 p = 1) : d49102 p ≤ (-1 : Int) + d48997 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28853 (p : Pattern) (guard : d0 p = 1) : d49102 p ≤ (-2 : Int) + d48997 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28854 (p : Pattern) (guard : d0 p = 1) : d49102 p ≤ (-1 : Int) + d192961 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28855 (p : Pattern) (guard : d0 p = 1) : d49102 p ≤ (-2 : Int) + d192961 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28856 (p : Pattern) (guard : d0 p = 1) : d49102 p ≤ (-1 : Int) + d48308 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28857 (p : Pattern) (guard : d0 p = 1) : d49102 p ≤ (-2 : Int) + d48308 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28858 (p : Pattern) (guard : d197838 p = 1) : d47866 p ≤ (1 : Int) + d47866 p := by
  omega
theorem compare28859 (p : Pattern) (guard : d198213 p = 1) : d47866 p ≤ (0 : Int) + d47866 p := by
  omega
theorem compare28860 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-1 : Int) + d208030 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28861 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-2 : Int) + d208030 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28862 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-1 : Int) + d49782 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28863 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-2 : Int) + d49782 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28864 (p : Pattern) (guard : d0 p = 1) : d49280 p ≤ (-1 : Int) + d48388 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28865 (p : Pattern) (guard : d0 p = 1) : d49280 p ≤ (-2 : Int) + d48388 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28866 (p : Pattern) (guard : d0 p = 1) : d49280 p ≤ (1 : Int) + d212576 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28867 (p : Pattern) (guard : d0 p = 1) : d49280 p ≤ (0 : Int) + d212576 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28868 (p : Pattern) (guard : d0 p = 1) : d49280 p ≤ (-1 : Int) + d49782 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28869 (p : Pattern) (guard : d0 p = 1) : d49280 p ≤ (-2 : Int) + d49782 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28870 (p : Pattern) (guard : d0 p = 1) : d49280 p ≤ (-1 : Int) + d216729 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28871 (p : Pattern) (guard : d0 p = 1) : d49280 p ≤ (-2 : Int) + d216729 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28872 (p : Pattern) (guard : d0 p = 1) : d49280 p ≤ (-1 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28873 (p : Pattern) (guard : d0 p = 1) : d49280 p ≤ (-2 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28874 (p : Pattern) (guard : d0 p = 1) : d49280 p ≤ (1 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28875 (p : Pattern) (guard : d0 p = 1) : d49280 p ≤ (0 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28876 (p : Pattern) (guard : d0 p = 1) : d49280 p ≤ (-1 : Int) + d48547 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28877 (p : Pattern) (guard : d0 p = 1) : d49280 p ≤ (-2 : Int) + d48547 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28878 (p : Pattern) (guard : d0 p = 1) : d49102 p ≤ (-1 : Int) + d48749 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28879 (p : Pattern) (guard : d0 p = 1) : d49102 p ≤ (-2 : Int) + d48749 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28880 (p : Pattern) (guard : d0 p = 1) : d49102 p ≤ (0 : Int) + d49102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28881 (p : Pattern) (guard : d0 p = 1) : d49102 p ≤ (-1 : Int) + d48547 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28882 (p : Pattern) (guard : d0 p = 1) : d49102 p ≤ (-2 : Int) + d48547 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28883 (p : Pattern) (guard : d0 p = 1) : d49102 p ≤ (1 : Int) + d225614 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28884 (p : Pattern) (guard : d0 p = 1) : d49102 p ≤ (0 : Int) + d225614 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28885 (p : Pattern) (guard : d240078 p = 1) : d47866 p ≤ (4 : Int) + d47866 p := by
  omega
theorem compare28886 (p : Pattern) (guard : d240211 p = 1) : d47866 p ≤ (3 : Int) + d47866 p := by
  omega
theorem compare28887 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (4 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28888 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (3 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28889 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-1 : Int) + d50101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28890 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-2 : Int) + d50101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28891 (p : Pattern) (guard : d250749 p = 1) : d47866 p ≤ (1 : Int) + d47866 p := by
  omega
theorem compare28892 (p : Pattern) (guard : d251096 p = 1) : d47866 p ≤ (0 : Int) + d47866 p := by
  omega
theorem compare28893 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28894 (p : Pattern) (guard : d0 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28895 (p : Pattern) (guard : d0 p = 1) : d47697 p ≤ (-1 : Int) + d253344 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28896 (p : Pattern) (guard : d0 p = 1) : d47676 p ≤ (-1 : Int) + d253323 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28897 (p : Pattern) (guard : d0 p = 1) : d47681 p ≤ (-1 : Int) + d253328 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28898 (p : Pattern) (guard : d0 p = 1) : d47655 p ≤ (-1 : Int) + d253304 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28899 (p : Pattern) (guard : d0 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28900 (p : Pattern) (guard : d0 p = 1) : d4 p ≤ (-1 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28901 (p : Pattern) (guard : d44880 p = 1) : d4 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44880, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28900 p hg
    simpa only [d44880, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13 p = 1 := by simpa only [d44880, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4620 p hg
    simpa only [d44880, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28902 (p : Pattern) (guard : d0 p = 1) : d47616 p ≤ (-1 : Int) + d47616 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28903 (p : Pattern) (guard : d46864 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 246 with
  | false =>
    have hg : d44880 p = 1 := by simpa only [d46864, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28901 p hg
    simpa only [d46864, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46864, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28902 p hg
    simpa only [d46864, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28904 (p : Pattern) (guard : d46865 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 226 with
  | false =>
    have hg : d46864 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28903 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28905 (p : Pattern) (guard : d46866 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 225 with
  | false =>
    have hg : d46865 p = 1 := by simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28904 p hg
    simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28906 (p : Pattern) (guard : d258695 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46866 p = 1 := by simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28905 p hg
    simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28907 (p : Pattern) (guard : d258696 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258695 p = 1 := by simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28906 p hg
    simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28908 (p : Pattern) (guard : d258697 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258696 p = 1 := by simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28907 p hg
    simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28909 (p : Pattern) (guard : d258698 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258697 p = 1 := by simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28908 p hg
    simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28910 (p : Pattern) (guard : d258699 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258698 p = 1 := by simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28909 p hg
    simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28911 (p : Pattern) (guard : d0 p = 1) : d47618 p ≤ (-1 : Int) + d253275 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28912 (p : Pattern) (guard : d258700 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258699 p = 1 := by simpa only [d258700, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28910 p hg
    simpa only [d258700, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258700, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28911 p hg
    simpa only [d258700, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28913 (p : Pattern) (guard : d0 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28914 (p : Pattern) (guard : d258701 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258700 p = 1 := by simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28912 p hg
    simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28913 p hg
    simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28915 (p : Pattern) (guard : d0 p = 1) : d47659 p ≤ (-1 : Int) + d253306 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28916 (p : Pattern) (guard : d258702 p = 1) : d47660 p ≤ (-1 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258701 p = 1 := by simpa only [d258702, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28914 p hg
    simpa only [d258702, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258702, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28915 p hg
    simpa only [d258702, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28917 (p : Pattern) (guard : d0 p = 1) : d47662 p ≤ (-1 : Int) + d253309 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28918 (p : Pattern) (guard : d258703 p = 1) : d47663 p ≤ (-1 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258702 p = 1 := by simpa only [d258703, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28916 p hg
    simpa only [d258703, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258703, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28917 p hg
    simpa only [d258703, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28919 (p : Pattern) (guard : d258704 p = 1) : d47664 p ≤ (-1 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258704, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28898 p hg
    simpa only [d258704, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258703 p = 1 := by simpa only [d258704, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28918 p hg
    simpa only [d258704, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28920 (p : Pattern) (guard : d0 p = 1) : d47684 p ≤ (-1 : Int) + d253331 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28921 (p : Pattern) (guard : d258705 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258704 p = 1 := by simpa only [d258705, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28919 p hg
    simpa only [d258705, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258705, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28920 p hg
    simpa only [d258705, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28922 (p : Pattern) (guard : d0 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28923 (p : Pattern) (guard : d258706 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258705 p = 1 := by simpa only [d258706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28921 p hg
    simpa only [d258706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28922 p hg
    simpa only [d258706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28924 (p : Pattern) (guard : d258707 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 158 with
  | false =>
    have hg : d258706 p = 1 := by simpa only [d258707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28923 p hg
    simpa only [d258707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28922 p hg
    simpa only [d258707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28925 (p : Pattern) (guard : d258708 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 157 with
  | false =>
    have hg : d258707 p = 1 := by simpa only [d258708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28924 p hg
    simpa only [d258708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28922 p hg
    simpa only [d258708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28926 (p : Pattern) (guard : d258709 p = 1) : d47686 p ≤ (-1 : Int) + d253333 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258709, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28897 p hg
    simpa only [d258709, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258708 p = 1 := by simpa only [d258709, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28925 p hg
    simpa only [d258709, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28927 (p : Pattern) (guard : d258710 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258710, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28896 p hg
    simpa only [d258710, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258709 p = 1 := by simpa only [d258710, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28926 p hg
    simpa only [d258710, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28928 (p : Pattern) (guard : d0 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28929 (p : Pattern) (guard : d258711 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 136 with
  | false =>
    have hg : d258710 p = 1 := by simpa only [d258711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28927 p hg
    simpa only [d258711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28928 p hg
    simpa only [d258711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28930 (p : Pattern) (guard : d258712 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 135 with
  | false =>
    have hg : d258711 p = 1 := by simpa only [d258712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28929 p hg
    simpa only [d258712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28928 p hg
    simpa only [d258712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28931 (p : Pattern) (guard : d258713 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 119 with
  | false =>
    have hg : d258712 p = 1 := by simpa only [d258713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28930 p hg
    simpa only [d258713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28928 p hg
    simpa only [d258713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28932 (p : Pattern) (guard : d0 p = 1) : d47698 p ≤ (-1 : Int) + d253345 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28933 (p : Pattern) (guard : d258714 p = 1) : d47699 p ≤ (-1 : Int) + d253346 p := by
  cases selected : p 116 with
  | false =>
    have hg : d258713 p = 1 := by simpa only [d258714, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28931 p hg
    simpa only [d258714, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258714, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28932 p hg
    simpa only [d258714, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28934 (p : Pattern) (guard : d258715 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258715, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28895 p hg
    simpa only [d258715, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258714 p = 1 := by simpa only [d258715, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28933 p hg
    simpa only [d258715, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28935 (p : Pattern) (guard : d258716 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d258715 p = 1 := by simpa only [d258716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28934 p hg
    simpa only [d258716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28936 (p : Pattern) (guard : d258717 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d258716 p = 1 := by simpa only [d258717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28935 p hg
    simpa only [d258717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28937 (p : Pattern) (guard : d258718 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d258717 p = 1 := by simpa only [d258718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28936 p hg
    simpa only [d258718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28938 (p : Pattern) (guard : d258719 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258718 p = 1 := by simpa only [d258719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28937 p hg
    simpa only [d258719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28939 (p : Pattern) (guard : d258720 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258719 p = 1 := by simpa only [d258720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28938 p hg
    simpa only [d258720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28940 (p : Pattern) (guard : d258721 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d258720 p = 1 := by simpa only [d258721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28939 p hg
    simpa only [d258721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28941 (p : Pattern) (guard : d258722 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258721 p = 1 := by simpa only [d258722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28940 p hg
    simpa only [d258722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28942 (p : Pattern) (guard : d258723 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258722 p = 1 := by simpa only [d258723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28941 p hg
    simpa only [d258723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28943 (p : Pattern) (guard : d258724 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258723 p = 1 := by simpa only [d258724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28942 p hg
    simpa only [d258724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28944 (p : Pattern) (guard : d258725 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258724 p = 1 := by simpa only [d258725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28943 p hg
    simpa only [d258725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28945 (p : Pattern) (guard : d258726 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d258718 p = 1 := by simpa only [d258726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28937 p hg
    simpa only [d258726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28946 (p : Pattern) (guard : d258727 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258726 p = 1 := by simpa only [d258727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28945 p hg
    simpa only [d258727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28947 (p : Pattern) (guard : d258728 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d258727 p = 1 := by simpa only [d258728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28946 p hg
    simpa only [d258728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28948 (p : Pattern) (guard : d258729 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258728 p = 1 := by simpa only [d258729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28947 p hg
    simpa only [d258729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28949 (p : Pattern) (guard : d258730 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258729 p = 1 := by simpa only [d258730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28948 p hg
    simpa only [d258730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28950 (p : Pattern) (guard : d258731 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258730 p = 1 := by simpa only [d258731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28949 p hg
    simpa only [d258731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28951 (p : Pattern) (guard : d258732 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d258724 p = 1 := by simpa only [d258732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28943 p hg
    simpa only [d258732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258731 p = 1 := by simpa only [d258732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28950 p hg
    simpa only [d258732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28952 (p : Pattern) (guard : d258733 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d258725 p = 1 := by simpa only [d258733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28944 p hg
    simpa only [d258733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258732 p = 1 := by simpa only [d258733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28951 p hg
    simpa only [d258733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28953 (p : Pattern) (guard : d258734 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 69 with
  | false =>
    have hg : d258733 p = 1 := by simpa only [d258734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28952 p hg
    simpa only [d258734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28954 (p : Pattern) (guard : d258735 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 51 with
  | false =>
    have hg : d258734 p = 1 := by simpa only [d258735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28953 p hg
    simpa only [d258735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28955 (p : Pattern) (guard : d258736 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d258736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258735 p = 1 := by simpa only [d258736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28954 p hg
    simpa only [d258736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28956 (p : Pattern) (guard : d0 p = 1) : d47767 p ≤ (-1 : Int) + d253406 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28957 (p : Pattern) (guard : d0 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28958 (p : Pattern) (guard : d0 p = 1) : d47763 p ≤ (-1 : Int) + d253402 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28959 (p : Pattern) (guard : d0 p = 1) : d47746 p ≤ (-1 : Int) + d253385 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28960 (p : Pattern) (guard : d0 p = 1) : d47751 p ≤ (-1 : Int) + d253390 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28961 (p : Pattern) (guard : d0 p = 1) : d47734 p ≤ (-1 : Int) + d253373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28962 (p : Pattern) (guard : d0 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28963 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (-1 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28964 (p : Pattern) (guard : d44880 p = 1) : d5 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44880, d47705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28963 p hg
    simpa only [d44880, d47705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13 p = 1 := by simpa only [d44880, d47705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4679 p hg
    simpa only [d44880, d47705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28965 (p : Pattern) (guard : d0 p = 1) : d47705 p ≤ (-1 : Int) + d47705 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28966 (p : Pattern) (guard : d46864 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 246 with
  | false =>
    have hg : d44880 p = 1 := by simpa only [d46864, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28964 p hg
    simpa only [d46864, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46864, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28965 p hg
    simpa only [d46864, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28967 (p : Pattern) (guard : d46865 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 226 with
  | false =>
    have hg : d46864 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28966 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28968 (p : Pattern) (guard : d46866 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 225 with
  | false =>
    have hg : d46865 p = 1 := by simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28967 p hg
    simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d46866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28969 (p : Pattern) (guard : d258695 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46866 p = 1 := by simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28968 p hg
    simpa only [d258695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28970 (p : Pattern) (guard : d258696 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258695 p = 1 := by simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28969 p hg
    simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d258696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28971 (p : Pattern) (guard : d258697 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258696 p = 1 := by simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28970 p hg
    simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d258697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28972 (p : Pattern) (guard : d258698 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258697 p = 1 := by simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28971 p hg
    simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d258698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28973 (p : Pattern) (guard : d258699 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258698 p = 1 := by simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28972 p hg
    simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d258699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28974 (p : Pattern) (guard : d0 p = 1) : d47707 p ≤ (-1 : Int) + d253350 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28975 (p : Pattern) (guard : d258700 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258699 p = 1 := by simpa only [d258700, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28973 p hg
    simpa only [d258700, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258700, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28974 p hg
    simpa only [d258700, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28976 (p : Pattern) (guard : d0 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28977 (p : Pattern) (guard : d258701 p = 1) : d47708 p ≤ (-1 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258700 p = 1 := by simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28975 p hg
    simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28976 p hg
    simpa only [d258701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28978 (p : Pattern) (guard : d0 p = 1) : d47661 p ≤ (-1 : Int) + d253308 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28979 (p : Pattern) (guard : d258702 p = 1) : d47735 p ≤ (-1 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258701 p = 1 := by simpa only [d258702, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28977 p hg
    simpa only [d258702, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258702, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d258702, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28980 (p : Pattern) (guard : d258703 p = 1) : d47736 p ≤ (-1 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258702 p = 1 := by simpa only [d258703, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28979 p hg
    simpa only [d258703, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258703, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d258703, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28981 (p : Pattern) (guard : d258704 p = 1) : d47737 p ≤ (-1 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258704, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28961 p hg
    simpa only [d258704, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258703 p = 1 := by simpa only [d258704, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28980 p hg
    simpa only [d258704, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28982 (p : Pattern) (guard : d0 p = 1) : d47754 p ≤ (-1 : Int) + d253393 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28983 (p : Pattern) (guard : d258705 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258704 p = 1 := by simpa only [d258705, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28981 p hg
    simpa only [d258705, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258705, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28982 p hg
    simpa only [d258705, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28984 (p : Pattern) (guard : d0 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28985 (p : Pattern) (guard : d258706 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258705 p = 1 := by simpa only [d258706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28983 p hg
    simpa only [d258706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28984 p hg
    simpa only [d258706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28986 (p : Pattern) (guard : d258707 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d258706 p = 1 := by simpa only [d258707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28985 p hg
    simpa only [d258707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28984 p hg
    simpa only [d258707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28987 (p : Pattern) (guard : d258708 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 157 with
  | false =>
    have hg : d258707 p = 1 := by simpa only [d258708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28986 p hg
    simpa only [d258708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28984 p hg
    simpa only [d258708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28988 (p : Pattern) (guard : d258709 p = 1) : d47756 p ≤ (-1 : Int) + d253395 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258709, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28960 p hg
    simpa only [d258709, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258708 p = 1 := by simpa only [d258709, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28987 p hg
    simpa only [d258709, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28989 (p : Pattern) (guard : d258710 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258710, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28959 p hg
    simpa only [d258710, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258709 p = 1 := by simpa only [d258710, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28988 p hg
    simpa only [d258710, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28990 (p : Pattern) (guard : d0 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28991 (p : Pattern) (guard : d258711 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 136 with
  | false =>
    have hg : d258710 p = 1 := by simpa only [d258711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28989 p hg
    simpa only [d258711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28990 p hg
    simpa only [d258711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28992 (p : Pattern) (guard : d258712 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 135 with
  | false =>
    have hg : d258711 p = 1 := by simpa only [d258712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28991 p hg
    simpa only [d258712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28990 p hg
    simpa only [d258712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28993 (p : Pattern) (guard : d258713 p = 1) : d47757 p ≤ (-1 : Int) + d253396 p := by
  cases selected : p 119 with
  | false =>
    have hg : d258712 p = 1 := by simpa only [d258713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28992 p hg
    simpa only [d258713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28990 p hg
    simpa only [d258713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28994 (p : Pattern) (guard : d0 p = 1) : d47764 p ≤ (-1 : Int) + d253403 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare28995 (p : Pattern) (guard : d258714 p = 1) : d47765 p ≤ (-1 : Int) + d253404 p := by
  cases selected : p 116 with
  | false =>
    have hg : d258713 p = 1 := by simpa only [d258714, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28993 p hg
    simpa only [d258714, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258714, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28994 p hg
    simpa only [d258714, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28996 (p : Pattern) (guard : d258715 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258715, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28958 p hg
    simpa only [d258715, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258714 p = 1 := by simpa only [d258715, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28995 p hg
    simpa only [d258715, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28997 (p : Pattern) (guard : d258716 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 113 with
  | false =>
    have hg : d258715 p = 1 := by simpa only [d258716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28996 p hg
    simpa only [d258716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28998 (p : Pattern) (guard : d258717 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 96 with
  | false =>
    have hg : d258716 p = 1 := by simpa only [d258717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28997 p hg
    simpa only [d258717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28999 (p : Pattern) (guard : d258718 p = 1) : d47766 p ≤ (-1 : Int) + d253405 p := by
  cases selected : p 95 with
  | false =>
    have hg : d258717 p = 1 := by simpa only [d258718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28998 p hg
    simpa only [d258718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28957 p hg
    simpa only [d258718, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
