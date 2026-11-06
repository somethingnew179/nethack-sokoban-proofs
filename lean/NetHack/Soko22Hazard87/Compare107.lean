import NetHack.Soko22Hazard87.Compare106
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare26750 (p : Pattern) (guard : d10076 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10074 p = 1 := by simpa only [d10076, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26749 p hg
    simpa only [d10076, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10076, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d10076, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26751 (p : Pattern) (guard : d16787 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16787, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d16787, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10076 p = 1 := by simpa only [d16787, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26750 p hg
    simpa only [d16787, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26752 (p : Pattern) (guard : d16788 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16787 p = 1 := by simpa only [d16788, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26751 p hg
    simpa only [d16788, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16788, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d16788, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26753 (p : Pattern) (guard : d16789 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1558 p = 1 := by simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26747 p hg
    simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16788 p = 1 := by simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26752 p hg
    simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26754 (p : Pattern) (guard : d10080 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26735 p hg
    simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10058 p = 1 := by simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26718 p hg
    simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26755 (p : Pattern) (guard : d10081 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1550 p = 1 := by simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26739 p hg
    simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26756 (p : Pattern) (guard : d10082 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d10080 p = 1 := by simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26754 p hg
    simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10081 p = 1 := by simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26755 p hg
    simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26757 (p : Pattern) (guard : d10083 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10082 p = 1 := by simpa only [d10083, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26756 p hg
    simpa only [d10083, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10083, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d10083, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26758 (p : Pattern) (guard : d1563 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1547 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26715 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26759 (p : Pattern) (guard : d5128 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1563 p = 1 := by simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26758 p hg
    simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26760 (p : Pattern) (guard : d5129 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5128 p = 1 := by simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26759 p hg
    simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26761 (p : Pattern) (guard : d1564 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1563 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26758 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26762 (p : Pattern) (guard : d1565 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1564 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26761 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26763 (p : Pattern) (guard : d5130 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d5129 p = 1 := by simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26760 p hg
    simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26762 p hg
    simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26764 (p : Pattern) (guard : d1578 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1565 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26762 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26765 (p : Pattern) (guard : d5131 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5130 p = 1 := by simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26763 p hg
    simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1578 p = 1 := by simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26764 p hg
    simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26766 (p : Pattern) (guard : d5132 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5131 p = 1 := by simpa only [d5132, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26765 p hg
    simpa only [d5132, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5132, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d5132, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26767 (p : Pattern) (guard : d10084 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10083 p = 1 := by simpa only [d10084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26757 p hg
    simpa only [d10084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5132 p = 1 := by simpa only [d10084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26766 p hg
    simpa only [d10084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26768 (p : Pattern) (guard : d10085 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10084 p = 1 := by simpa only [d10085, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26767 p hg
    simpa only [d10085, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10085, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d10085, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26769 (p : Pattern) (guard : d10087 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10085 p = 1 := by simpa only [d10087, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26768 p hg
    simpa only [d10087, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10087, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d10087, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26770 (p : Pattern) (guard : d15156 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15156, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d15156, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10087 p = 1 := by simpa only [d15156, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26769 p hg
    simpa only [d15156, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26771 (p : Pattern) (guard : d15157 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15156 p = 1 := by simpa only [d15157, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26770 p hg
    simpa only [d15157, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15157, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d15157, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26772 (p : Pattern) (guard : d16790 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15152 p = 1 := by simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26726 p hg
    simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15157 p = 1 := by simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26771 p hg
    simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26773 (p : Pattern) (guard : d16791 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16789 p = 1 := by simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26753 p hg
    simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16790 p = 1 := by simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26772 p hg
    simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26774 (p : Pattern) (guard : d16864 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16863 p = 1 := by simpa only [d16864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26728 p hg
    simpa only [d16864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16791 p = 1 := by simpa only [d16864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26773 p hg
    simpa only [d16864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26775 (p : Pattern) (guard : d19288 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d16864 p = 1 := by simpa only [d19288, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d19288, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19288, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d19288, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26776 (p : Pattern) (guard : d19289 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19289, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d19289, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19288 p = 1 := by simpa only [d19289, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26775 p hg
    simpa only [d19289, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26777 (p : Pattern) (guard : d10095 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1529 p = 1 := by simpa only [d10095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26679 p hg
    simpa only [d10095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10056 p = 1 := by simpa only [d10095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26714 p hg
    simpa only [d10095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26778 (p : Pattern) (guard : d10096 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d10095 p = 1 := by simpa only [d10096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26777 p hg
    simpa only [d10096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d10096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26779 (p : Pattern) (guard : d10097 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10096 p = 1 := by simpa only [d10097, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26778 p hg
    simpa only [d10097, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10097, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d10097, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26780 (p : Pattern) (guard : d10098 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10097 p = 1 := by simpa only [d10098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26779 p hg
    simpa only [d10098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10061 p = 1 := by simpa only [d10098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26721 p hg
    simpa only [d10098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26781 (p : Pattern) (guard : d10099 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10098 p = 1 := by simpa only [d10099, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26780 p hg
    simpa only [d10099, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10099, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d10099, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26782 (p : Pattern) (guard : d10101 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10099 p = 1 := by simpa only [d10101, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26781 p hg
    simpa only [d10101, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10101, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d10101, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26783 (p : Pattern) (guard : d13348 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d13348, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d13348, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10101 p = 1 := by simpa only [d13348, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26782 p hg
    simpa only [d13348, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26784 (p : Pattern) (guard : d13349 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13348 p = 1 := by simpa only [d13349, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26783 p hg
    simpa only [d13349, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13349, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d13349, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26785 (p : Pattern) (guard : d16867 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13349 p = 1 := by simpa only [d16867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26784 p hg
    simpa only [d16867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15157 p = 1 := by simpa only [d16867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26771 p hg
    simpa only [d16867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26786 (p : Pattern) (guard : d15158 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15157 p = 1 := by simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26771 p hg
    simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26787 (p : Pattern) (guard : d16868 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16867 p = 1 := by simpa only [d16868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26785 p hg
    simpa only [d16868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15158 p = 1 := by simpa only [d16868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26786 p hg
    simpa only [d16868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26788 (p : Pattern) (guard : d16869 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16791 p = 1 := by simpa only [d16869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26773 p hg
    simpa only [d16869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16868 p = 1 := by simpa only [d16869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26787 p hg
    simpa only [d16869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26789 (p : Pattern) (guard : d19290 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d16869 p = 1 := by simpa only [d19290, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26788 p hg
    simpa only [d19290, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19290, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d19290, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26790 (p : Pattern) (guard : d19291 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19291, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d19291, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19290 p = 1 := by simpa only [d19291, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26789 p hg
    simpa only [d19291, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26791 (p : Pattern) (guard : d19292 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d19289 p = 1 := by simpa only [d19292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26776 p hg
    simpa only [d19292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19291 p = 1 := by simpa only [d19292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26790 p hg
    simpa only [d19292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26792 (p : Pattern) (guard : d1559 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1541 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26731 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26793 (p : Pattern) (guard : d1560 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26737 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26792 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26794 (p : Pattern) (guard : d1561 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1560 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26793 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26323 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26795 (p : Pattern) (guard : d1562 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26735 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1561 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26794 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26796 (p : Pattern) (guard : d1566 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1550 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26739 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26762 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26797 (p : Pattern) (guard : d1567 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1562 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26795 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1566 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26796 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26798 (p : Pattern) (guard : d1568 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1567 p = 1 := by simpa only [d1568, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26797 p hg
    simpa only [d1568, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1568, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d1568, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26799 (p : Pattern) (guard : d1569 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26742 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1568 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26798 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26800 (p : Pattern) (guard : d1570 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1569 p = 1 := by simpa only [d1570, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26799 p hg
    simpa only [d1570, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1570, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d1570, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26801 (p : Pattern) (guard : d1571 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1570 p = 1 := by simpa only [d1571, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26800 p hg
    simpa only [d1571, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1571, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d1571, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26802 (p : Pattern) (guard : d1572 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1572, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d1572, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1571 p = 1 := by simpa only [d1572, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26801 p hg
    simpa only [d1572, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26803 (p : Pattern) (guard : d1573 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1572 p = 1 := by simpa only [d1573, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26802 p hg
    simpa only [d1573, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1573, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d1573, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26804 (p : Pattern) (guard : d10114 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1568 p = 1 := by simpa only [d10114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26798 p hg
    simpa only [d10114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5132 p = 1 := by simpa only [d10114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26766 p hg
    simpa only [d10114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26805 (p : Pattern) (guard : d10115 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10114 p = 1 := by simpa only [d10115, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26804 p hg
    simpa only [d10115, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10115, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d10115, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26806 (p : Pattern) (guard : d10117 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10115 p = 1 := by simpa only [d10117, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26805 p hg
    simpa only [d10117, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10117, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d10117, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26807 (p : Pattern) (guard : d16792 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16792, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d16792, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10117 p = 1 := by simpa only [d16792, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26806 p hg
    simpa only [d16792, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26808 (p : Pattern) (guard : d16793 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16792 p = 1 := by simpa only [d16793, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26807 p hg
    simpa only [d16793, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16793, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d16793, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26809 (p : Pattern) (guard : d16794 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1573 p = 1 := by simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26803 p hg
    simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16793 p = 1 := by simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26808 p hg
    simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26810 (p : Pattern) (guard : d16795 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16794 p = 1 := by simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26809 p hg
    simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15158 p = 1 := by simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26786 p hg
    simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26811 (p : Pattern) (guard : d16796 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16791 p = 1 := by simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26773 p hg
    simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16795 p = 1 := by simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26810 p hg
    simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26812 (p : Pattern) (guard : d19293 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d16796 p = 1 := by simpa only [d19293, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26811 p hg
    simpa only [d19293, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19293, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d19293, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26813 (p : Pattern) (guard : d19294 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19294, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d19294, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19293 p = 1 := by simpa only [d19294, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26812 p hg
    simpa only [d19294, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26814 (p : Pattern) (guard : d5123 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5122 p = 1 := by simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26716 p hg
    simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1563 p = 1 := by simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26758 p hg
    simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26815 (p : Pattern) (guard : d5124 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5123 p = 1 := by simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26814 p hg
    simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26816 (p : Pattern) (guard : d5125 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26735 p hg
    simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5124 p = 1 := by simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26815 p hg
    simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26817 (p : Pattern) (guard : d5126 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5125 p = 1 := by simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26816 p hg
    simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1566 p = 1 := by simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26796 p hg
    simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26818 (p : Pattern) (guard : d5127 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5126 p = 1 := by simpa only [d5127, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26817 p hg
    simpa only [d5127, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5127, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d5127, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26819 (p : Pattern) (guard : d5133 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5127 p = 1 := by simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26818 p hg
    simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5132 p = 1 := by simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26766 p hg
    simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26820 (p : Pattern) (guard : d5134 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5133 p = 1 := by simpa only [d5134, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26819 p hg
    simpa only [d5134, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5134, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d5134, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26821 (p : Pattern) (guard : d5135 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5134 p = 1 := by simpa only [d5135, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26820 p hg
    simpa only [d5135, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5135, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d5135, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26822 (p : Pattern) (guard : d5136 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5136, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d5136, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5135 p = 1 := by simpa only [d5136, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26821 p hg
    simpa only [d5136, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26823 (p : Pattern) (guard : d5137 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5136 p = 1 := by simpa only [d5137, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26822 p hg
    simpa only [d5137, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5137, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d5137, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26824 (p : Pattern) (guard : d5138 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5137 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26823 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26825 (p : Pattern) (guard : d1575 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26792 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26826 (p : Pattern) (guard : d1576 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1575 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26825 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26323 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26827 (p : Pattern) (guard : d1593 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26826 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26828 (p : Pattern) (guard : d10129 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1559 p = 1 := by simpa only [d10129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26792 p hg
    simpa only [d10129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d10129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26829 (p : Pattern) (guard : d10130 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d10129 p = 1 := by simpa only [d10130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26828 p hg
    simpa only [d10130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19 p = 1 := by simpa only [d10130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25504 p hg
    simpa only [d10130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26830 (p : Pattern) (guard : d10131 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d10130 p = 1 := by simpa only [d10131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26829 p hg
    simpa only [d10131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d10131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26831 (p : Pattern) (guard : d10132 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1593 p = 1 := by simpa only [d10132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26827 p hg
    simpa only [d10132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10131 p = 1 := by simpa only [d10132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26830 p hg
    simpa only [d10132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26832 (p : Pattern) (guard : d10133 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10132 p = 1 := by simpa only [d10133, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26831 p hg
    simpa only [d10133, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10133, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d10133, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26833 (p : Pattern) (guard : d10134 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10133 p = 1 := by simpa only [d10134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26832 p hg
    simpa only [d10134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25510 p hg
    simpa only [d10134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26834 (p : Pattern) (guard : d10135 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10134 p = 1 := by simpa only [d10135, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26833 p hg
    simpa only [d10135, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10135, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d10135, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26835 (p : Pattern) (guard : d10137 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10135 p = 1 := by simpa only [d10137, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26834 p hg
    simpa only [d10137, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10137, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d10137, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26836 (p : Pattern) (guard : d15163 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15163, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d15163, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10137 p = 1 := by simpa only [d15163, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26835 p hg
    simpa only [d15163, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26837 (p : Pattern) (guard : d15164 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15163 p = 1 := by simpa only [d15164, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26836 p hg
    simpa only [d15164, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15164, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d15164, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26838 (p : Pattern) (guard : d15165 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15164 p = 1 := by simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26837 p hg
    simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26839 (p : Pattern) (guard : d15166 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5138 p = 1 := by simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26824 p hg
    simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15165 p = 1 := by simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26838 p hg
    simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26840 (p : Pattern) (guard : d16799 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26810 p hg
    simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15166 p = 1 := by simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26839 p hg
    simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26841 (p : Pattern) (guard : d19295 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d16799 p = 1 := by simpa only [d19295, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26840 p hg
    simpa only [d19295, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19295, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d19295, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26842 (p : Pattern) (guard : d19296 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19296, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d19296, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19295 p = 1 := by simpa only [d19296, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26841 p hg
    simpa only [d19296, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26843 (p : Pattern) (guard : d19297 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d19294 p = 1 := by simpa only [d19297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26813 p hg
    simpa only [d19297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19296 p = 1 := by simpa only [d19297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26842 p hg
    simpa only [d19297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26844 (p : Pattern) (guard : d19298 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d19292 p = 1 := by simpa only [d19298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26791 p hg
    simpa only [d19298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19297 p = 1 := by simpa only [d19298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26843 p hg
    simpa only [d19298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26845 (p : Pattern) (guard : d188128 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16873 p = 1 := by simpa only [d188128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26665 p hg
    simpa only [d188128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19298 p = 1 := by simpa only [d188128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26844 p hg
    simpa only [d188128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26846 (p : Pattern) (guard : d188129 p = 1) : d48705 p ≤ (-1 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d188128 p = 1 := by simpa only [d188129, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26845 p hg
    simpa only [d188129, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188129, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25527 p hg
    simpa only [d188129, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26847 (p : Pattern) (guard : d188130 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188130, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25461 p hg
    simpa only [d188130, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188129 p = 1 := by simpa only [d188130, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26846 p hg
    simpa only [d188130, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26848 (p : Pattern) (guard : d16877 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16801 p = 1 := by simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26663 p hg
    simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d16877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26849 (p : Pattern) (guard : d16878 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16802 p = 1 := by simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26664 p hg
    simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16877 p = 1 := by simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26848 p hg
    simpa only [d16878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26850 (p : Pattern) (guard : d19304 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d19296 p = 1 := by simpa only [d19304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26842 p hg
    simpa only [d19304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d19304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26851 (p : Pattern) (guard : d19305 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d19297 p = 1 := by simpa only [d19305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26843 p hg
    simpa only [d19305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19304 p = 1 := by simpa only [d19305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26850 p hg
    simpa only [d19305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26852 (p : Pattern) (guard : d188131 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16878 p = 1 := by simpa only [d188131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26849 p hg
    simpa only [d188131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19305 p = 1 := by simpa only [d188131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26851 p hg
    simpa only [d188131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26853 (p : Pattern) (guard : d188132 p = 1) : d48705 p ≤ (-1 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d188131 p = 1 := by simpa only [d188132, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26852 p hg
    simpa only [d188132, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188132, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25527 p hg
    simpa only [d188132, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26854 (p : Pattern) (guard : d188133 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188133, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25461 p hg
    simpa only [d188133, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188132 p = 1 := by simpa only [d188133, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26853 p hg
    simpa only [d188133, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26855 (p : Pattern) (guard : d188134 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d188130 p = 1 := by simpa only [d188134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26847 p hg
    simpa only [d188134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188133 p = 1 := by simpa only [d188134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26854 p hg
    simpa only [d188134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26856 (p : Pattern) (guard : d188135 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d188134 p = 1 := by simpa only [d188135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26855 p hg
    simpa only [d188135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26857 (p : Pattern) (guard : d188136 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d188135 p = 1 := by simpa only [d188136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26856 p hg
    simpa only [d188136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26858 (p : Pattern) (guard : d188137 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d188136 p = 1 := by simpa only [d188137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26857 p hg
    simpa only [d188137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26859 (p : Pattern) (guard : d1577 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26647 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26583 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26860 (p : Pattern) (guard : d1579 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1577 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26859 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1578 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26585 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26861 (p : Pattern) (guard : d1580 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1579 p = 1 := by simpa only [d1580, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26860 p hg
    simpa only [d1580, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1580, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d1580, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26862 (p : Pattern) (guard : d1581 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1568 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26619 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1580 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26861 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26863 (p : Pattern) (guard : d1582 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1581 p = 1 := by simpa only [d1582, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26862 p hg
    simpa only [d1582, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1582, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d1582, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26864 (p : Pattern) (guard : d1583 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1582 p = 1 := by simpa only [d1583, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26863 p hg
    simpa only [d1583, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1583, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d1583, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26865 (p : Pattern) (guard : d1584 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1584, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d1584, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1583 p = 1 := by simpa only [d1584, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26864 p hg
    simpa only [d1584, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26866 (p : Pattern) (guard : d1585 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1584 p = 1 := by simpa only [d1585, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26865 p hg
    simpa only [d1585, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1585, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d1585, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26867 (p : Pattern) (guard : d1588 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1585 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26866 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26868 (p : Pattern) (guard : d15171 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1588 p = 1 := by simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26867 p hg
    simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15165 p = 1 := by simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26659 p hg
    simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26869 (p : Pattern) (guard : d16803 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26631 p hg
    simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15171 p = 1 := by simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26868 p hg
    simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26870 (p : Pattern) (guard : d16804 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16804, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d16804, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16803 p = 1 := by simpa only [d16804, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26869 p hg
    simpa only [d16804, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26871 (p : Pattern) (guard : d16805 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16805, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d16805, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16804 p = 1 := by simpa only [d16805, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26870 p hg
    simpa only [d16805, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26872 (p : Pattern) (guard : d16806 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16805 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26871 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26873 (p : Pattern) (guard : d16811 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16806 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26872 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26874 (p : Pattern) (guard : d1577 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26826 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26762 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26875 (p : Pattern) (guard : d1579 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1577 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26874 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1578 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26764 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26876 (p : Pattern) (guard : d1580 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1579 p = 1 := by simpa only [d1580, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26875 p hg
    simpa only [d1580, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1580, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d1580, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26877 (p : Pattern) (guard : d1581 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1568 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26798 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1580 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26876 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26878 (p : Pattern) (guard : d1582 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1581 p = 1 := by simpa only [d1582, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26877 p hg
    simpa only [d1582, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1582, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d1582, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26879 (p : Pattern) (guard : d1583 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1582 p = 1 := by simpa only [d1583, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26878 p hg
    simpa only [d1583, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1583, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d1583, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26880 (p : Pattern) (guard : d1584 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1584, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d1584, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1583 p = 1 := by simpa only [d1584, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26879 p hg
    simpa only [d1584, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26881 (p : Pattern) (guard : d1585 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1584 p = 1 := by simpa only [d1585, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26880 p hg
    simpa only [d1585, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1585, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d1585, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26882 (p : Pattern) (guard : d1588 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1585 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26881 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26883 (p : Pattern) (guard : d15171 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1588 p = 1 := by simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26882 p hg
    simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15165 p = 1 := by simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26838 p hg
    simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26884 (p : Pattern) (guard : d16803 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26810 p hg
    simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15171 p = 1 := by simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26883 p hg
    simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26885 (p : Pattern) (guard : d19323 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d16803 p = 1 := by simpa only [d19323, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26884 p hg
    simpa only [d19323, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19323, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d19323, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26886 (p : Pattern) (guard : d19324 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19324, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d19324, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19323 p = 1 := by simpa only [d19324, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26885 p hg
    simpa only [d19324, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26887 (p : Pattern) (guard : d19325 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d19324 p = 1 := by simpa only [d19325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26886 p hg
    simpa only [d19325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d19325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26888 (p : Pattern) (guard : d19326 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d19325 p = 1 := by simpa only [d19326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26887 p hg
    simpa only [d19326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d19326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26889 (p : Pattern) (guard : d188138 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16811 p = 1 := by simpa only [d188138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26873 p hg
    simpa only [d188138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19326 p = 1 := by simpa only [d188138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26888 p hg
    simpa only [d188138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26890 (p : Pattern) (guard : d188139 p = 1) : d48705 p ≤ (-1 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d188138 p = 1 := by simpa only [d188139, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26889 p hg
    simpa only [d188139, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188139, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25527 p hg
    simpa only [d188139, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26891 (p : Pattern) (guard : d188140 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188140, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25461 p hg
    simpa only [d188140, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188139 p = 1 := by simpa only [d188140, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26890 p hg
    simpa only [d188140, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26892 (p : Pattern) (guard : d188141 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d188133 p = 1 := by simpa only [d188141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26854 p hg
    simpa only [d188141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188140 p = 1 := by simpa only [d188141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26891 p hg
    simpa only [d188141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26893 (p : Pattern) (guard : d188142 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d188141 p = 1 := by simpa only [d188142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26892 p hg
    simpa only [d188142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26894 (p : Pattern) (guard : d188143 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d188142 p = 1 := by simpa only [d188143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26893 p hg
    simpa only [d188143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26895 (p : Pattern) (guard : d188144 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d188143 p = 1 := by simpa only [d188144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26894 p hg
    simpa only [d188144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26896 (p : Pattern) (guard : d188145 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d188137 p = 1 := by simpa only [d188145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26858 p hg
    simpa only [d188145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188144 p = 1 := by simpa only [d188145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26895 p hg
    simpa only [d188145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26897 (p : Pattern) (guard : d188146 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d188145 p = 1 := by simpa only [d188146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26896 p hg
    simpa only [d188146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26898 (p : Pattern) (guard : d13287 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1588 p = 1 := by simpa only [d13287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26867 p hg
    simpa only [d13287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d13287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26899 (p : Pattern) (guard : d16929 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26631 p hg
    simpa only [d16929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13287 p = 1 := by simpa only [d16929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26898 p hg
    simpa only [d16929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26900 (p : Pattern) (guard : d16930 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16930, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d16930, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16929 p = 1 := by simpa only [d16930, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26899 p hg
    simpa only [d16930, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26901 (p : Pattern) (guard : d16931 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16931, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d16931, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16930 p = 1 := by simpa only [d16931, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26900 p hg
    simpa only [d16931, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26902 (p : Pattern) (guard : d16932 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16931 p = 1 := by simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26901 p hg
    simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d16932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26903 (p : Pattern) (guard : d16933 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16802 p = 1 := by simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26664 p hg
    simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16932 p = 1 := by simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26902 p hg
    simpa only [d16933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26904 (p : Pattern) (guard : d13287 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1588 p = 1 := by simpa only [d13287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26882 p hg
    simpa only [d13287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d13287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26905 (p : Pattern) (guard : d16929 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26810 p hg
    simpa only [d16929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13287 p = 1 := by simpa only [d16929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26904 p hg
    simpa only [d16929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26906 (p : Pattern) (guard : d19418 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d16929 p = 1 := by simpa only [d19418, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26905 p hg
    simpa only [d19418, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19418, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d19418, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26907 (p : Pattern) (guard : d19419 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19419, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d19419, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19418 p = 1 := by simpa only [d19419, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26906 p hg
    simpa only [d19419, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26908 (p : Pattern) (guard : d19420 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d19419 p = 1 := by simpa only [d19420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26907 p hg
    simpa only [d19420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d19420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26909 (p : Pattern) (guard : d19421 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d19297 p = 1 := by simpa only [d19421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26843 p hg
    simpa only [d19421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19420 p = 1 := by simpa only [d19421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26908 p hg
    simpa only [d19421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26910 (p : Pattern) (guard : d188147 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16933 p = 1 := by simpa only [d188147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26903 p hg
    simpa only [d188147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19421 p = 1 := by simpa only [d188147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26909 p hg
    simpa only [d188147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26911 (p : Pattern) (guard : d188148 p = 1) : d48705 p ≤ (-1 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d188147 p = 1 := by simpa only [d188148, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26910 p hg
    simpa only [d188148, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188148, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25527 p hg
    simpa only [d188148, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26912 (p : Pattern) (guard : d188149 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188149, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25461 p hg
    simpa only [d188149, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188148 p = 1 := by simpa only [d188149, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26911 p hg
    simpa only [d188149, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26913 (p : Pattern) (guard : d188150 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d188149 p = 1 := by simpa only [d188150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26912 p hg
    simpa only [d188150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26914 (p : Pattern) (guard : d188151 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d188150 p = 1 := by simpa only [d188151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26913 p hg
    simpa only [d188151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26915 (p : Pattern) (guard : d188152 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d188151 p = 1 := by simpa only [d188152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26914 p hg
    simpa only [d188152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26916 (p : Pattern) (guard : d188153 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d188152 p = 1 := by simpa only [d188153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26915 p hg
    simpa only [d188153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26917 (p : Pattern) (guard : d188154 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d188153 p = 1 := by simpa only [d188154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26916 p hg
    simpa only [d188154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26918 (p : Pattern) (guard : d188155 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d188154 p = 1 := by simpa only [d188155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26917 p hg
    simpa only [d188155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26919 (p : Pattern) (guard : d188156 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 89 with
  | false =>
    have hg : d188146 p = 1 := by simpa only [d188156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26897 p hg
    simpa only [d188156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188155 p = 1 := by simpa only [d188156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26918 p hg
    simpa only [d188156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26920 (p : Pattern) (guard : d188157 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188156 p = 1 := by simpa only [d188157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26919 p hg
    simpa only [d188157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26921 (p : Pattern) (guard : d188158 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188157 p = 1 := by simpa only [d188158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26920 p hg
    simpa only [d188158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26922 (p : Pattern) (guard : d188159 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188159, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25459 p hg
    simpa only [d188159, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188158 p = 1 := by simpa only [d188159, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26921 p hg
    simpa only [d188159, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26923 (p : Pattern) (guard : d188160 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d188160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188159 p = 1 := by simpa only [d188160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26922 p hg
    simpa only [d188160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26924 (p : Pattern) (guard : d188161 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d188140 p = 1 := by simpa only [d188161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26891 p hg
    simpa only [d188161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26925 (p : Pattern) (guard : d188162 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d188161 p = 1 := by simpa only [d188162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26924 p hg
    simpa only [d188162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26926 (p : Pattern) (guard : d188163 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d188162 p = 1 := by simpa only [d188163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26925 p hg
    simpa only [d188163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26927 (p : Pattern) (guard : d188164 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d188163 p = 1 := by simpa only [d188164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26926 p hg
    simpa only [d188164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26928 (p : Pattern) (guard : d188165 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d188164 p = 1 := by simpa only [d188165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26927 p hg
    simpa only [d188165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26929 (p : Pattern) (guard : d188166 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188165 p = 1 := by simpa only [d188166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26928 p hg
    simpa only [d188166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26930 (p : Pattern) (guard : d188167 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 89 with
  | false =>
    have hg : d188166 p = 1 := by simpa only [d188167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26929 p hg
    simpa only [d188167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26931 (p : Pattern) (guard : d188168 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188167 p = 1 := by simpa only [d188168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26930 p hg
    simpa only [d188168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26932 (p : Pattern) (guard : d188169 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188168 p = 1 := by simpa only [d188169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26931 p hg
    simpa only [d188169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26933 (p : Pattern) (guard : d188170 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188170, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25459 p hg
    simpa only [d188170, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188169 p = 1 := by simpa only [d188170, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26932 p hg
    simpa only [d188170, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26934 (p : Pattern) (guard : d188171 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d188171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188170 p = 1 := by simpa only [d188171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26933 p hg
    simpa only [d188171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26935 (p : Pattern) (guard : d188172 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 69 with
  | false =>
    have hg : d188160 p = 1 := by simpa only [d188172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26923 p hg
    simpa only [d188172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188171 p = 1 := by simpa only [d188172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26934 p hg
    simpa only [d188172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26936 (p : Pattern) (guard : d188173 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 51 with
  | false =>
    have hg : d188172 p = 1 := by simpa only [d188173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26935 p hg
    simpa only [d188173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d188173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26937 (p : Pattern) (guard : d188174 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 50 with
  | false =>
    have hg : d188173 p = 1 := by simpa only [d188174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26936 p hg
    simpa only [d188174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d188174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26938 (p : Pattern) (guard : d188175 p = 1) : d48748 p ≤ (-1 : Int) + d188517 p := by
  cases selected : p 49 with
  | false =>
    have hg : d188174 p = 1 := by simpa only [d188175, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26937 p hg
    simpa only [d188175, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188175, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25544 p hg
    simpa only [d188175, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26939 (p : Pattern) (guard : d188176 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188176, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25457 p hg
    simpa only [d188176, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188175 p = 1 := by simpa only [d188176, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26938 p hg
    simpa only [d188176, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26940 (p : Pattern) (guard : d188177 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188176 p = 1 := by simpa only [d188177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26939 p hg
    simpa only [d188177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26941 (p : Pattern) (guard : d188178 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188177 p = 1 := by simpa only [d188178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26940 p hg
    simpa only [d188178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26942 (p : Pattern) (guard : d188179 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188178 p = 1 := by simpa only [d188179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26941 p hg
    simpa only [d188179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26943 (p : Pattern) (guard : d188180 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188179 p = 1 := by simpa only [d188180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26942 p hg
    simpa only [d188180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26944 (p : Pattern) (guard : d188181 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188180 p = 1 := by simpa only [d188181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26943 p hg
    simpa only [d188181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26945 (p : Pattern) (guard : d188182 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188181 p = 1 := by simpa only [d188182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26944 p hg
    simpa only [d188182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26946 (p : Pattern) (guard : d188183 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188182 p = 1 := by simpa only [d188183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26945 p hg
    simpa only [d188183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26947 (p : Pattern) (guard : d188184 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188183 p = 1 := by simpa only [d188184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26946 p hg
    simpa only [d188184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26948 (p : Pattern) (guard : d188185 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188184 p = 1 := by simpa only [d188185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26947 p hg
    simpa only [d188185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26949 (p : Pattern) (guard : d188186 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d188127 p = 1 := by simpa only [d188186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26486 p hg
    simpa only [d188186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188185 p = 1 := by simpa only [d188186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26948 p hg
    simpa only [d188186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26950 (p : Pattern) (guard : d1997 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25623 p hg
    simpa only [d1997, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25466 p hg
    simpa only [d1997, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26951 (p : Pattern) (guard : d1998 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26950 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26952 (p : Pattern) (guard : d1999 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1998 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26951 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26953 (p : Pattern) (guard : d2000 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1999 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26952 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26954 (p : Pattern) (guard : d2001 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1523 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26494 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26955 (p : Pattern) (guard : d2002 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2001 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26954 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26956 (p : Pattern) (guard : d2003 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2002 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26955 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26957 (p : Pattern) (guard : d2004 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2000 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26953 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2003 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26956 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26958 (p : Pattern) (guard : d2007 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2006 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26532 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26959 (p : Pattern) (guard : d2008 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2007 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26958 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26960 (p : Pattern) (guard : d2009 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2004 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26957 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2008 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26959 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26961 (p : Pattern) (guard : d2010 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2009 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26960 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26962 (p : Pattern) (guard : d2011 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2010 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26961 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26963 (p : Pattern) (guard : d2012 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2011 p = 1 := by simpa only [d2012, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26962 p hg
    simpa only [d2012, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2012, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d2012, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26964 (p : Pattern) (guard : d2143 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25478 p hg
    simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2012 p = 1 := by simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26963 p hg
    simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26965 (p : Pattern) (guard : d2144 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2143 p = 1 := by simpa only [d2144, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26964 p hg
    simpa only [d2144, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2144, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d2144, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26966 (p : Pattern) (guard : d2145 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2144 p = 1 := by simpa only [d2145, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26965 p hg
    simpa only [d2145, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2145, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d2145, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26967 (p : Pattern) (guard : d2146 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2146, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d2146, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2145 p = 1 := by simpa only [d2146, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26966 p hg
    simpa only [d2146, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26968 (p : Pattern) (guard : d2147 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2146 p = 1 := by simpa only [d2147, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26967 p hg
    simpa only [d2147, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2147, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d2147, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26969 (p : Pattern) (guard : d10342 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2012 p = 1 := by simpa only [d10342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26963 p hg
    simpa only [d10342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25478 p hg
    simpa only [d10342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26970 (p : Pattern) (guard : d10343 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10342 p = 1 := by simpa only [d10343, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26969 p hg
    simpa only [d10343, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10343, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d10343, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26971 (p : Pattern) (guard : d10345 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10343 p = 1 := by simpa only [d10345, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26970 p hg
    simpa only [d10345, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10345, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d10345, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26972 (p : Pattern) (guard : d17225 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17225, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d17225, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10345 p = 1 := by simpa only [d17225, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26971 p hg
    simpa only [d17225, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26973 (p : Pattern) (guard : d17226 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17225 p = 1 := by simpa only [d17226, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26972 p hg
    simpa only [d17226, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17226, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d17226, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26974 (p : Pattern) (guard : d17227 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2147 p = 1 := by simpa only [d17227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26968 p hg
    simpa only [d17227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17226 p = 1 := by simpa only [d17227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26973 p hg
    simpa only [d17227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26975 (p : Pattern) (guard : d10349 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2009 p = 1 := by simpa only [d10349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26960 p hg
    simpa only [d10349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d10349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26976 (p : Pattern) (guard : d10350 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d10349 p = 1 := by simpa only [d10350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26975 p hg
    simpa only [d10350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d10350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26977 (p : Pattern) (guard : d10351 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10350 p = 1 := by simpa only [d10351, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26976 p hg
    simpa only [d10351, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10351, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d10351, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26978 (p : Pattern) (guard : d10352 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10351 p = 1 := by simpa only [d10352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26977 p hg
    simpa only [d10352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25478 p hg
    simpa only [d10352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26979 (p : Pattern) (guard : d10353 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10352 p = 1 := by simpa only [d10353, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26978 p hg
    simpa only [d10353, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10353, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d10353, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26980 (p : Pattern) (guard : d10355 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10353 p = 1 := by simpa only [d10355, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26979 p hg
    simpa only [d10355, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10355, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d10355, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26981 (p : Pattern) (guard : d13675 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d13675, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d13675, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10355 p = 1 := by simpa only [d13675, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26980 p hg
    simpa only [d13675, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26982 (p : Pattern) (guard : d13676 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13675 p = 1 := by simpa only [d13676, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26981 p hg
    simpa only [d13676, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13676, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d13676, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26983 (p : Pattern) (guard : d17228 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d17228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13676 p = 1 := by simpa only [d17228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26982 p hg
    simpa only [d17228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26984 (p : Pattern) (guard : d17229 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17227 p = 1 := by simpa only [d17229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26974 p hg
    simpa only [d17229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17228 p = 1 := by simpa only [d17229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26983 p hg
    simpa only [d17229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26985 (p : Pattern) (guard : d2013 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26950 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26986 (p : Pattern) (guard : d2014 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26951 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26985 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26987 (p : Pattern) (guard : d2015 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1999 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26952 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26986 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26988 (p : Pattern) (guard : d2016 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d2016, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25551 p hg
    simpa only [d2016, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2016, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25466 p hg
    simpa only [d2016, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26989 (p : Pattern) (guard : d2017 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26950 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2016 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26988 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26990 (p : Pattern) (guard : d2018 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2017 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26989 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26991 (p : Pattern) (guard : d2019 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2002 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26955 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2018 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26990 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26992 (p : Pattern) (guard : d2020 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2015 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26987 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2019 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26991 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26993 (p : Pattern) (guard : d2021 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d2016 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26988 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26994 (p : Pattern) (guard : d2022 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2021 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26993 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26995 (p : Pattern) (guard : d2023 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2006 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26532 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2022 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26994 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26996 (p : Pattern) (guard : d2024 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2023 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26995 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26997 (p : Pattern) (guard : d2025 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2020 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26992 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2024 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26996 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26998 (p : Pattern) (guard : d2026 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2009 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26960 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2025 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26997 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26999 (p : Pattern) (guard : d2027 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26985 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
