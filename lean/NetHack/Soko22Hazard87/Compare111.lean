import NetHack.Soko22Hazard87.Compare110
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare27750 (p : Pattern) (guard : d9452 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5011 p = 1 := by simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27749 p hg
    simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27751 (p : Pattern) (guard : d9453 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d9452 p = 1 := by simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27750 p hg
    simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27752 (p : Pattern) (guard : d9454 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d9453 p = 1 := by simpa only [d9454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27751 p hg
    simpa only [d9454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d9454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27448 p hg
    simpa only [d9454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27753 (p : Pattern) (guard : d9455 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9454 p = 1 := by simpa only [d9455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27752 p hg
    simpa only [d9455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d9455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27754 (p : Pattern) (guard : d9456 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9455 p = 1 := by simpa only [d9456, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27753 p hg
    simpa only [d9456, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9456, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d9456, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27755 (p : Pattern) (guard : d9457 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317 p = 1 := by simpa only [d9457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27612 p hg
    simpa only [d9457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9456 p = 1 := by simpa only [d9457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27754 p hg
    simpa only [d9457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27756 (p : Pattern) (guard : d9458 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9457 p = 1 := by simpa only [d9458, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27755 p hg
    simpa only [d9458, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9458, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d9458, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27757 (p : Pattern) (guard : d9460 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9458 p = 1 := by simpa only [d9460, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27756 p hg
    simpa only [d9460, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9460, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d9460, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27758 (p : Pattern) (guard : d16073 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16073, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d16073, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9460 p = 1 := by simpa only [d16073, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27757 p hg
    simpa only [d16073, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27759 (p : Pattern) (guard : d16074 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16073 p = 1 := by simpa only [d16074, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27758 p hg
    simpa only [d16074, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16074, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d16074, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27760 (p : Pattern) (guard : d16075 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d546 p = 1 := by simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27747 p hg
    simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16074 p = 1 := by simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27759 p hg
    simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27761 (p : Pattern) (guard : d9464 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d314 p = 1 := by simpa only [d9464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27609 p hg
    simpa only [d9464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9453 p = 1 := by simpa only [d9464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27751 p hg
    simpa only [d9464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27762 (p : Pattern) (guard : d9465 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9464 p = 1 := by simpa only [d9465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27761 p hg
    simpa only [d9465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d9465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27763 (p : Pattern) (guard : d9466 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9465 p = 1 := by simpa only [d9466, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27762 p hg
    simpa only [d9466, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9466, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d9466, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27764 (p : Pattern) (guard : d9467 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9466 p = 1 := by simpa only [d9467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27763 p hg
    simpa only [d9467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9456 p = 1 := by simpa only [d9467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27754 p hg
    simpa only [d9467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27765 (p : Pattern) (guard : d9468 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9467 p = 1 := by simpa only [d9468, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27764 p hg
    simpa only [d9468, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9468, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d9468, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27766 (p : Pattern) (guard : d9470 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9468 p = 1 := by simpa only [d9470, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27765 p hg
    simpa only [d9470, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9470, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d9470, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27767 (p : Pattern) (guard : d12748 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d12748, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d12748, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9470 p = 1 := by simpa only [d12748, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27766 p hg
    simpa only [d12748, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27768 (p : Pattern) (guard : d12749 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12748 p = 1 := by simpa only [d12749, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27767 p hg
    simpa only [d12749, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12749, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d12749, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27769 (p : Pattern) (guard : d750 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27530 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27453 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27770 (p : Pattern) (guard : d751 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d750 p = 1 := by simpa only [d751, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27769 p hg
    simpa only [d751, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d751, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d751, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27771 (p : Pattern) (guard : d752 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d751 p = 1 := by simpa only [d752, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27770 p hg
    simpa only [d752, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d752, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d752, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27772 (p : Pattern) (guard : d753 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d753, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d753, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d752 p = 1 := by simpa only [d753, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27771 p hg
    simpa only [d753, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27773 (p : Pattern) (guard : d754 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27772 p hg
    simpa only [d754, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d754, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27774 (p : Pattern) (guard : d12750 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12749 p = 1 := by simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27768 p hg
    simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27773 p hg
    simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27775 (p : Pattern) (guard : d16227 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16075 p = 1 := by simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27760 p hg
    simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12750 p = 1 := by simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27774 p hg
    simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27776 (p : Pattern) (guard : d755 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27617 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27773 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27777 (p : Pattern) (guard : d757 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d754 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27773 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27778 (p : Pattern) (guard : d758 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d755 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27776 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d757 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27777 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27779 (p : Pattern) (guard : d16228 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16227 p = 1 := by simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27775 p hg
    simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27778 p hg
    simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27780 (p : Pattern) (guard : d18873 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d16228 p = 1 := by simpa only [d18873, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27779 p hg
    simpa only [d18873, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18873, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d18873, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27781 (p : Pattern) (guard : d18874 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d18874, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d18874, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18873 p = 1 := by simpa only [d18874, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27780 p hg
    simpa only [d18874, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27782 (p : Pattern) (guard : d762 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27777 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27783 (p : Pattern) (guard : d763 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27778 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d762 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27782 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27784 (p : Pattern) (guard : d18875 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d763 p = 1 := by simpa only [d18875, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27783 p hg
    simpa only [d18875, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18875, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d18875, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27785 (p : Pattern) (guard : d18876 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d18876, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d18876, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18875 p = 1 := by simpa only [d18876, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27784 p hg
    simpa only [d18876, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27786 (p : Pattern) (guard : d18877 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d18874 p = 1 := by simpa only [d18877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27781 p hg
    simpa only [d18877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18876 p = 1 := by simpa only [d18877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27785 p hg
    simpa only [d18877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27787 (p : Pattern) (guard : d18884 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d18876 p = 1 := by simpa only [d18884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27785 p hg
    simpa only [d18884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d18884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27788 (p : Pattern) (guard : d18885 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d18877 p = 1 := by simpa only [d18885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27786 p hg
    simpa only [d18885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18884 p = 1 := by simpa only [d18885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27787 p hg
    simpa only [d18885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27789 (p : Pattern) (guard : d188019 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16232 p = 1 := by simpa only [d188019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27728 p hg
    simpa only [d188019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18885 p = 1 := by simpa only [d188019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27788 p hg
    simpa only [d188019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27790 (p : Pattern) (guard : d188020 p = 1) : d48705 p ≤ (-2 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d188019 p = 1 := by simpa only [d188020, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27789 p hg
    simpa only [d188020, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188020, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27470 p hg
    simpa only [d188020, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27791 (p : Pattern) (guard : d188021 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188021, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27404 p hg
    simpa only [d188021, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188020 p = 1 := by simpa only [d188021, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27790 p hg
    simpa only [d188021, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27792 (p : Pattern) (guard : d772 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27727 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27793 (p : Pattern) (guard : d18894 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d18884 p = 1 := by simpa only [d18894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27787 p hg
    simpa only [d18894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d18894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27794 (p : Pattern) (guard : d188026 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d772 p = 1 := by simpa only [d188026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27792 p hg
    simpa only [d188026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18894 p = 1 := by simpa only [d188026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27793 p hg
    simpa only [d188026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27795 (p : Pattern) (guard : d188027 p = 1) : d48705 p ≤ (-2 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d188026 p = 1 := by simpa only [d188027, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27794 p hg
    simpa only [d188027, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188027, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27470 p hg
    simpa only [d188027, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27796 (p : Pattern) (guard : d188028 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188028, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27404 p hg
    simpa only [d188028, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188027 p = 1 := by simpa only [d188028, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27795 p hg
    simpa only [d188028, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27797 (p : Pattern) (guard : d188029 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d188021 p = 1 := by simpa only [d188029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27791 p hg
    simpa only [d188029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188028 p = 1 := by simpa only [d188029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27796 p hg
    simpa only [d188029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27798 (p : Pattern) (guard : d188030 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d188029 p = 1 := by simpa only [d188030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27797 p hg
    simpa only [d188030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27799 (p : Pattern) (guard : d188031 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d188030 p = 1 := by simpa only [d188031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27798 p hg
    simpa only [d188031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27800 (p : Pattern) (guard : d188032 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d188031 p = 1 := by simpa only [d188032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27799 p hg
    simpa only [d188032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27801 (p : Pattern) (guard : d188046 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d188028 p = 1 := by simpa only [d188046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27796 p hg
    simpa only [d188046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27802 (p : Pattern) (guard : d188047 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d188046 p = 1 := by simpa only [d188047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27801 p hg
    simpa only [d188047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27803 (p : Pattern) (guard : d188048 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d188047 p = 1 := by simpa only [d188048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27802 p hg
    simpa only [d188048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27804 (p : Pattern) (guard : d188049 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d188048 p = 1 := by simpa only [d188049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27803 p hg
    simpa only [d188049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27805 (p : Pattern) (guard : d188336 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d188032 p = 1 := by simpa only [d188336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27800 p hg
    simpa only [d188336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188049 p = 1 := by simpa only [d188336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27804 p hg
    simpa only [d188336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27806 (p : Pattern) (guard : d188337 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188336 p = 1 := by simpa only [d188337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27805 p hg
    simpa only [d188337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27807 (p : Pattern) (guard : d188338 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 89 with
  | false =>
    have hg : d188337 p = 1 := by simpa only [d188338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27806 p hg
    simpa only [d188338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27808 (p : Pattern) (guard : d188339 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188338 p = 1 := by simpa only [d188339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27807 p hg
    simpa only [d188339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27809 (p : Pattern) (guard : d188340 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188339 p = 1 := by simpa only [d188340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27808 p hg
    simpa only [d188340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27810 (p : Pattern) (guard : d188341 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188341, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27402 p hg
    simpa only [d188341, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188340 p = 1 := by simpa only [d188341, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27809 p hg
    simpa only [d188341, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27811 (p : Pattern) (guard : d188342 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188341 p = 1 := by simpa only [d188342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27810 p hg
    simpa only [d188342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27812 (p : Pattern) (guard : d188343 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 69 with
  | false =>
    have hg : d188342 p = 1 := by simpa only [d188343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27811 p hg
    simpa only [d188343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27813 (p : Pattern) (guard : d188344 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 51 with
  | false =>
    have hg : d188343 p = 1 := by simpa only [d188344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27812 p hg
    simpa only [d188344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27814 (p : Pattern) (guard : d188345 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 50 with
  | false =>
    have hg : d188344 p = 1 := by simpa only [d188345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27813 p hg
    simpa only [d188345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27815 (p : Pattern) (guard : d188346 p = 1) : d48748 p ≤ (-2 : Int) + d188517 p := by
  cases selected : p 49 with
  | false =>
    have hg : d188345 p = 1 := by simpa only [d188346, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27814 p hg
    simpa only [d188346, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188346, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27487 p hg
    simpa only [d188346, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27816 (p : Pattern) (guard : d188347 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188347, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27400 p hg
    simpa only [d188347, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188346 p = 1 := by simpa only [d188347, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27815 p hg
    simpa only [d188347, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27817 (p : Pattern) (guard : d188348 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188347 p = 1 := by simpa only [d188348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27816 p hg
    simpa only [d188348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27818 (p : Pattern) (guard : d188349 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188348 p = 1 := by simpa only [d188349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27817 p hg
    simpa only [d188349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27819 (p : Pattern) (guard : d188350 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188349 p = 1 := by simpa only [d188350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27818 p hg
    simpa only [d188350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27820 (p : Pattern) (guard : d188351 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188350 p = 1 := by simpa only [d188351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27819 p hg
    simpa only [d188351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27821 (p : Pattern) (guard : d188352 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188351 p = 1 := by simpa only [d188352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27820 p hg
    simpa only [d188352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27822 (p : Pattern) (guard : d188353 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188352 p = 1 := by simpa only [d188353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27821 p hg
    simpa only [d188353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27823 (p : Pattern) (guard : d188354 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188353 p = 1 := by simpa only [d188354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27822 p hg
    simpa only [d188354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27824 (p : Pattern) (guard : d188355 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d188335 p = 1 := by simpa only [d188355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27668 p hg
    simpa only [d188355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188354 p = 1 := by simpa only [d188355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27823 p hg
    simpa only [d188355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27825 (p : Pattern) (guard : d820 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d528 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27669 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27826 (p : Pattern) (guard : d821 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27825 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d529 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27670 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27827 (p : Pattern) (guard : d822 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d821 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27826 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27828 (p : Pattern) (guard : d823 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d822 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27827 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27829 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (-2 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27830 (p : Pattern) (guard : d1084 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1084, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27829 p hg
    simpa only [d1084, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d1084, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27497 p hg
    simpa only [d1084, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27831 (p : Pattern) (guard : d1085 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1084 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27830 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27832 (p : Pattern) (guard : d1086 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1085 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27831 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27833 (p : Pattern) (guard : d1087 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1086 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27832 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27834 (p : Pattern) (guard : d1088 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27671 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27833 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27835 (p : Pattern) (guard : d1089 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27834 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27836 (p : Pattern) (guard : d1090 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27828 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1089 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27835 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27837 (p : Pattern) (guard : d825 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27571 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27838 (p : Pattern) (guard : d826 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27669 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d825 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27837 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27839 (p : Pattern) (guard : d827 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27838 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d535 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27676 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27840 (p : Pattern) (guard : d828 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d827 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27839 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27841 (p : Pattern) (guard : d829 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27840 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27842 (p : Pattern) (guard : d830 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27841 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d538 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27679 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27843 (p : Pattern) (guard : d1091 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1090 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27836 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27842 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27844 (p : Pattern) (guard : d1092 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1091 p = 1 := by simpa only [d1092, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27843 p hg
    simpa only [d1092, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d1092, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27845 (p : Pattern) (guard : d1093 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27832 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27413 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27846 (p : Pattern) (guard : d1094 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27574 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27845 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27847 (p : Pattern) (guard : d1095 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27846 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27848 (p : Pattern) (guard : d1096 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1089 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27835 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27847 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27849 (p : Pattern) (guard : d1097 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27848 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27680 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27850 (p : Pattern) (guard : d1098 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1097 p = 1 := by simpa only [d1098, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27849 p hg
    simpa only [d1098, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1098, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d1098, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27851 (p : Pattern) (guard : d1099 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27844 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1098 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27850 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27852 (p : Pattern) (guard : d1100 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1099 p = 1 := by simpa only [d1100, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27851 p hg
    simpa only [d1100, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1100, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d1100, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27853 (p : Pattern) (guard : d1101 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1100 p = 1 := by simpa only [d1101, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27852 p hg
    simpa only [d1101, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1101, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d1101, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27854 (p : Pattern) (guard : d1102 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1102, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d1102, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1101 p = 1 := by simpa only [d1102, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27853 p hg
    simpa only [d1102, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27855 (p : Pattern) (guard : d1103 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1102 p = 1 := by simpa only [d1103, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27854 p hg
    simpa only [d1103, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1103, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d1103, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27856 (p : Pattern) (guard : d5121 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d825 p = 1 := by simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27837 p hg
    simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27857 (p : Pattern) (guard : d308 p = 1) : d2 p ≤ (-2 : Int) + d4 p := by
  have ha := bounds2 p
  have hb := bounds4 p
  omega
theorem compare27858 (p : Pattern) (guard : d1519 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 246 with
  | false =>
    have hg : d308 p = 1 := by simpa only [d1519, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27857 p hg
    simpa only [d1519, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1519, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27409 p hg
    simpa only [d1519, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27859 (p : Pattern) (guard : d1531 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27858 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27860 (p : Pattern) (guard : d9579 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d9579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27859 p hg
    simpa only [d9579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16 p = 1 := by simpa only [d9579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27412 p hg
    simpa only [d9579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27861 (p : Pattern) (guard : d9580 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5121 p = 1 := by simpa only [d9580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27856 p hg
    simpa only [d9580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9579 p = 1 := by simpa only [d9580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27860 p hg
    simpa only [d9580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27862 (p : Pattern) (guard : d9771 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27832 p hg
    simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27863 (p : Pattern) (guard : d9772 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d9580 p = 1 := by simpa only [d9772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27861 p hg
    simpa only [d9772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9771 p = 1 := by simpa only [d9772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27862 p hg
    simpa only [d9772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27864 (p : Pattern) (guard : d9773 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d9772 p = 1 := by simpa only [d9773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27863 p hg
    simpa only [d9773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d9773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27865 (p : Pattern) (guard : d9774 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d9773 p = 1 := by simpa only [d9774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27864 p hg
    simpa only [d9774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9453 p = 1 := by simpa only [d9774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27691 p hg
    simpa only [d9774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27866 (p : Pattern) (guard : d9775 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9774 p = 1 := by simpa only [d9775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27865 p hg
    simpa only [d9775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d9775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27867 (p : Pattern) (guard : d9776 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9775 p = 1 := by simpa only [d9776, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27866 p hg
    simpa only [d9776, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9776, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d9776, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27868 (p : Pattern) (guard : d9788 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1098 p = 1 := by simpa only [d9788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27850 p hg
    simpa only [d9788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9776 p = 1 := by simpa only [d9788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27867 p hg
    simpa only [d9788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27869 (p : Pattern) (guard : d9789 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9788 p = 1 := by simpa only [d9789, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27868 p hg
    simpa only [d9789, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9789, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d9789, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27870 (p : Pattern) (guard : d9791 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9789 p = 1 := by simpa only [d9791, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27869 p hg
    simpa only [d9791, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9791, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d9791, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27871 (p : Pattern) (guard : d16438 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16438, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d16438, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9791 p = 1 := by simpa only [d16438, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27870 p hg
    simpa only [d16438, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27872 (p : Pattern) (guard : d16439 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16438 p = 1 := by simpa only [d16439, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27871 p hg
    simpa only [d16439, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16439, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d16439, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27873 (p : Pattern) (guard : d16440 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1103 p = 1 := by simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27855 p hg
    simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16439 p = 1 := by simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27872 p hg
    simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27874 (p : Pattern) (guard : d9581 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d9580 p = 1 := by simpa only [d9581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27861 p hg
    simpa only [d9581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d9581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27875 (p : Pattern) (guard : d9582 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d9581 p = 1 := by simpa only [d9582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27874 p hg
    simpa only [d9582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d9582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27876 (p : Pattern) (guard : d9768 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1089 p = 1 := by simpa only [d9768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27835 p hg
    simpa only [d9768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9582 p = 1 := by simpa only [d9768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27875 p hg
    simpa only [d9768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27877 (p : Pattern) (guard : d9769 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9768 p = 1 := by simpa only [d9769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27876 p hg
    simpa only [d9769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d9769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27878 (p : Pattern) (guard : d9770 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9769 p = 1 := by simpa only [d9770, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27877 p hg
    simpa only [d9770, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9770, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d9770, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27879 (p : Pattern) (guard : d9777 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9770 p = 1 := by simpa only [d9777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27878 p hg
    simpa only [d9777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9776 p = 1 := by simpa only [d9777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27867 p hg
    simpa only [d9777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27880 (p : Pattern) (guard : d9778 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9777 p = 1 := by simpa only [d9778, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27879 p hg
    simpa only [d9778, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9778, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d9778, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27881 (p : Pattern) (guard : d9780 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9778 p = 1 := by simpa only [d9780, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27880 p hg
    simpa only [d9780, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9780, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d9780, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27882 (p : Pattern) (guard : d14758 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14758, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d14758, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9780 p = 1 := by simpa only [d14758, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27881 p hg
    simpa only [d14758, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27883 (p : Pattern) (guard : d14759 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14758 p = 1 := by simpa only [d14759, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27882 p hg
    simpa only [d14759, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14759, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d14759, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27884 (p : Pattern) (guard : d9795 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27847 p hg
    simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9453 p = 1 := by simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27691 p hg
    simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27885 (p : Pattern) (guard : d9796 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d134 p = 1 := by simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27503 p hg
    simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27886 (p : Pattern) (guard : d9797 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9795 p = 1 := by simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27884 p hg
    simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9796 p = 1 := by simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27885 p hg
    simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27887 (p : Pattern) (guard : d9798 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9797 p = 1 := by simpa only [d9798, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27886 p hg
    simpa only [d9798, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9798, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d9798, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27888 (p : Pattern) (guard : d1115 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27414 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27889 (p : Pattern) (guard : d1116 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1115 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27888 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27890 (p : Pattern) (guard : d1117 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27889 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27416 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27891 (p : Pattern) (guard : d1118 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1117 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27890 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27417 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27892 (p : Pattern) (guard : d1119 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1118 p = 1 := by simpa only [d1119, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27891 p hg
    simpa only [d1119, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1119, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d1119, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27893 (p : Pattern) (guard : d9799 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9798 p = 1 := by simpa only [d9799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27887 p hg
    simpa only [d9799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d9799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27892 p hg
    simpa only [d9799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27894 (p : Pattern) (guard : d9800 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9799 p = 1 := by simpa only [d9800, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27893 p hg
    simpa only [d9800, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9800, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d9800, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27895 (p : Pattern) (guard : d9802 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9800 p = 1 := by simpa only [d9802, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27894 p hg
    simpa only [d9802, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9802, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d9802, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27896 (p : Pattern) (guard : d14763 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14763, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d14763, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9802 p = 1 := by simpa only [d14763, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27895 p hg
    simpa only [d14763, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27897 (p : Pattern) (guard : d14764 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14763 p = 1 := by simpa only [d14764, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27896 p hg
    simpa only [d14764, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14764, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d14764, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27898 (p : Pattern) (guard : d16441 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14759 p = 1 := by simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27883 p hg
    simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14764 p = 1 := by simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27897 p hg
    simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27899 (p : Pattern) (guard : d16442 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16440 p = 1 := by simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27873 p hg
    simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16441 p = 1 := by simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27898 p hg
    simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27900 (p : Pattern) (guard : d1104 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27501 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27414 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27901 (p : Pattern) (guard : d1105 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1104 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27900 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27902 (p : Pattern) (guard : d1106 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27847 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1105 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27901 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27903 (p : Pattern) (guard : d1107 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1106 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27902 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27504 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27904 (p : Pattern) (guard : d1108 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1107 p = 1 := by simpa only [d1108, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27903 p hg
    simpa only [d1108, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1108, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d1108, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27905 (p : Pattern) (guard : d1109 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1098 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27850 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1108 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27904 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27906 (p : Pattern) (guard : d1110 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1109 p = 1 := by simpa only [d1110, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27905 p hg
    simpa only [d1110, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1110, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d1110, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27907 (p : Pattern) (guard : d1111 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1110 p = 1 := by simpa only [d1111, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27906 p hg
    simpa only [d1111, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1111, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d1111, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27908 (p : Pattern) (guard : d1112 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1112, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d1112, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1111 p = 1 := by simpa only [d1112, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27907 p hg
    simpa only [d1112, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27909 (p : Pattern) (guard : d1113 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1112 p = 1 := by simpa only [d1113, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27908 p hg
    simpa only [d1113, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1113, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d1113, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27910 (p : Pattern) (guard : d1120 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1108 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27904 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27892 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27911 (p : Pattern) (guard : d1121 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1120 p = 1 := by simpa only [d1121, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27910 p hg
    simpa only [d1121, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1121, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d1121, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27912 (p : Pattern) (guard : d1122 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1121 p = 1 := by simpa only [d1122, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27911 p hg
    simpa only [d1122, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d1122, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27913 (p : Pattern) (guard : d1123 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1123, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d1123, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1122 p = 1 := by simpa only [d1123, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27912 p hg
    simpa only [d1123, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27914 (p : Pattern) (guard : d1124 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1123 p = 1 := by simpa only [d1124, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27913 p hg
    simpa only [d1124, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1124, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d1124, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27915 (p : Pattern) (guard : d1125 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1113 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27909 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1124 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27914 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27916 (p : Pattern) (guard : d14765 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14764 p = 1 := by simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27897 p hg
    simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27917 (p : Pattern) (guard : d16443 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1125 p = 1 := by simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27915 p hg
    simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14765 p = 1 := by simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27916 p hg
    simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27918 (p : Pattern) (guard : d16444 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16442 p = 1 := by simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27899 p hg
    simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16443 p = 1 := by simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27917 p hg
    simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27919 (p : Pattern) (guard : d16445 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16445, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d16445, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16444 p = 1 := by simpa only [d16445, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27918 p hg
    simpa only [d16445, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27920 (p : Pattern) (guard : d16446 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16446, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d16446, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16445 p = 1 := by simpa only [d16446, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27919 p hg
    simpa only [d16446, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27921 (p : Pattern) (guard : d5012 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5011 p = 1 := by simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27689 p hg
    simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27414 p hg
    simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27922 (p : Pattern) (guard : d5013 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5012 p = 1 := by simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27921 p hg
    simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27923 (p : Pattern) (guard : d5014 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27847 p hg
    simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5013 p = 1 := by simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27922 p hg
    simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27924 (p : Pattern) (guard : d5015 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5014 p = 1 := by simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27923 p hg
    simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27504 p hg
    simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27925 (p : Pattern) (guard : d5016 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5015 p = 1 := by simpa only [d5016, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27924 p hg
    simpa only [d5016, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5016, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d5016, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27926 (p : Pattern) (guard : d5017 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5016 p = 1 := by simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27925 p hg
    simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27892 p hg
    simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27927 (p : Pattern) (guard : d5018 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5017 p = 1 := by simpa only [d5018, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27926 p hg
    simpa only [d5018, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5018, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d5018, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27928 (p : Pattern) (guard : d5019 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5018 p = 1 := by simpa only [d5019, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27927 p hg
    simpa only [d5019, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5019, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d5019, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27929 (p : Pattern) (guard : d5020 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5020, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d5020, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5019 p = 1 := by simpa only [d5020, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27928 p hg
    simpa only [d5020, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27930 (p : Pattern) (guard : d5021 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5020 p = 1 := by simpa only [d5021, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27929 p hg
    simpa only [d5021, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5021, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d5021, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27931 (p : Pattern) (guard : d5022 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5021 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27930 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27932 (p : Pattern) (guard : d1132 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27889 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27933 (p : Pattern) (guard : d9841 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d9841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27932 p hg
    simpa only [d9841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d9841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27417 p hg
    simpa only [d9841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27934 (p : Pattern) (guard : d9842 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9841 p = 1 := by simpa only [d9842, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27933 p hg
    simpa only [d9842, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9842, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d9842, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27935 (p : Pattern) (guard : d9843 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9842 p = 1 := by simpa only [d9843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27934 p hg
    simpa only [d9843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27421 p hg
    simpa only [d9843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27936 (p : Pattern) (guard : d9844 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9843 p = 1 := by simpa only [d9844, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27935 p hg
    simpa only [d9844, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9844, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d9844, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27937 (p : Pattern) (guard : d9846 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9844 p = 1 := by simpa only [d9846, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27936 p hg
    simpa only [d9846, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9846, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d9846, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27938 (p : Pattern) (guard : d14770 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14770, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d14770, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9846 p = 1 := by simpa only [d14770, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27937 p hg
    simpa only [d14770, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27939 (p : Pattern) (guard : d14771 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14770 p = 1 := by simpa only [d14771, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27938 p hg
    simpa only [d14771, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14771, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d14771, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27940 (p : Pattern) (guard : d14772 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14771 p = 1 := by simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27939 p hg
    simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27941 (p : Pattern) (guard : d14773 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5022 p = 1 := by simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27931 p hg
    simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14772 p = 1 := by simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27940 p hg
    simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27942 (p : Pattern) (guard : d16447 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27917 p hg
    simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14773 p = 1 := by simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27941 p hg
    simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27943 (p : Pattern) (guard : d16448 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16448, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d16448, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16447 p = 1 := by simpa only [d16448, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27942 p hg
    simpa only [d16448, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27944 (p : Pattern) (guard : d16449 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16449, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d16449, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16448 p = 1 := by simpa only [d16449, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27943 p hg
    simpa only [d16449, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27945 (p : Pattern) (guard : d16450 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16446 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27920 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16449 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27944 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27946 (p : Pattern) (guard : d1127 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1124 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27914 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27947 (p : Pattern) (guard : d14778 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1127 p = 1 := by simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27946 p hg
    simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14772 p = 1 := by simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27940 p hg
    simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27948 (p : Pattern) (guard : d16451 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27917 p hg
    simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14778 p = 1 := by simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27947 p hg
    simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27949 (p : Pattern) (guard : d16452 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16452, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d16452, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16451 p = 1 := by simpa only [d16452, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27948 p hg
    simpa only [d16452, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27950 (p : Pattern) (guard : d16453 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16453, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d16453, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16452 p = 1 := by simpa only [d16453, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27949 p hg
    simpa only [d16453, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27951 (p : Pattern) (guard : d16454 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16453 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27950 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27952 (p : Pattern) (guard : d16455 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16450 p = 1 := by simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27945 p hg
    simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16454 p = 1 := by simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27951 p hg
    simpa only [d16455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27953 (p : Pattern) (guard : d820 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d528 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27729 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27954 (p : Pattern) (guard : d821 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27953 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d529 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27730 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27955 (p : Pattern) (guard : d822 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d821 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27954 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27956 (p : Pattern) (guard : d823 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d822 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27955 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27957 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (-2 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare27958 (p : Pattern) (guard : d1084 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1084, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27957 p hg
    simpa only [d1084, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d1084, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27521 p hg
    simpa only [d1084, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27959 (p : Pattern) (guard : d1085 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1084 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27958 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27960 (p : Pattern) (guard : d1086 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1085 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27959 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27961 (p : Pattern) (guard : d1087 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1086 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27960 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27962 (p : Pattern) (guard : d1088 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27731 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27961 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27963 (p : Pattern) (guard : d1089 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27962 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27964 (p : Pattern) (guard : d1090 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27956 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1089 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27963 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27965 (p : Pattern) (guard : d825 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27604 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27966 (p : Pattern) (guard : d826 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27729 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d825 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27965 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27967 (p : Pattern) (guard : d827 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27966 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d535 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27736 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27968 (p : Pattern) (guard : d828 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d827 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27967 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27969 (p : Pattern) (guard : d829 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27968 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27970 (p : Pattern) (guard : d830 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27969 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d538 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27739 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27971 (p : Pattern) (guard : d1091 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1090 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27964 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27970 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27972 (p : Pattern) (guard : d1092 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1091 p = 1 := by simpa only [d1092, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27971 p hg
    simpa only [d1092, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d1092, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27973 (p : Pattern) (guard : d1093 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27960 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27445 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27974 (p : Pattern) (guard : d1094 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27607 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27973 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27975 (p : Pattern) (guard : d1095 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27974 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27976 (p : Pattern) (guard : d1096 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1089 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27963 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27975 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27977 (p : Pattern) (guard : d1097 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27976 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27740 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27978 (p : Pattern) (guard : d1098 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1097 p = 1 := by simpa only [d1098, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27977 p hg
    simpa only [d1098, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1098, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d1098, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27979 (p : Pattern) (guard : d1099 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27972 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1098 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27978 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27980 (p : Pattern) (guard : d1100 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1099 p = 1 := by simpa only [d1100, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27979 p hg
    simpa only [d1100, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1100, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d1100, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27981 (p : Pattern) (guard : d1101 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1100 p = 1 := by simpa only [d1101, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27980 p hg
    simpa only [d1101, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1101, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d1101, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27982 (p : Pattern) (guard : d1102 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1102, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d1102, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1101 p = 1 := by simpa only [d1102, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27981 p hg
    simpa only [d1102, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27983 (p : Pattern) (guard : d1103 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1102 p = 1 := by simpa only [d1103, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27982 p hg
    simpa only [d1103, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1103, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d1103, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27984 (p : Pattern) (guard : d5121 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d825 p = 1 := by simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27965 p hg
    simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27985 (p : Pattern) (guard : d308 p = 1) : d0 p ≤ (-2 : Int) + d2 p := by
  have ha := bounds0 p
  have hb := bounds2 p
  omega
theorem compare27986 (p : Pattern) (guard : d1519 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 246 with
  | false =>
    have hg : d308 p = 1 := by simpa only [d1519, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27985 p hg
    simpa only [d1519, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1519, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27441 p hg
    simpa only [d1519, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27987 (p : Pattern) (guard : d1531 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27986 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27988 (p : Pattern) (guard : d9579 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d9579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27987 p hg
    simpa only [d9579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16 p = 1 := by simpa only [d9579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27444 p hg
    simpa only [d9579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27989 (p : Pattern) (guard : d9580 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5121 p = 1 := by simpa only [d9580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27984 p hg
    simpa only [d9580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9579 p = 1 := by simpa only [d9580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27988 p hg
    simpa only [d9580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27990 (p : Pattern) (guard : d9771 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27960 p hg
    simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27991 (p : Pattern) (guard : d9772 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d9580 p = 1 := by simpa only [d9772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27989 p hg
    simpa only [d9772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9771 p = 1 := by simpa only [d9772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27990 p hg
    simpa only [d9772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27992 (p : Pattern) (guard : d9773 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d9772 p = 1 := by simpa only [d9773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27991 p hg
    simpa only [d9773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d9773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27993 (p : Pattern) (guard : d9774 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d9773 p = 1 := by simpa only [d9774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27992 p hg
    simpa only [d9774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9453 p = 1 := by simpa only [d9774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27751 p hg
    simpa only [d9774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27994 (p : Pattern) (guard : d9775 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9774 p = 1 := by simpa only [d9775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27993 p hg
    simpa only [d9775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d9775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27995 (p : Pattern) (guard : d9776 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9775 p = 1 := by simpa only [d9776, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27994 p hg
    simpa only [d9776, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9776, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d9776, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27996 (p : Pattern) (guard : d9788 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1098 p = 1 := by simpa only [d9788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27978 p hg
    simpa only [d9788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9776 p = 1 := by simpa only [d9788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27995 p hg
    simpa only [d9788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27997 (p : Pattern) (guard : d9789 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9788 p = 1 := by simpa only [d9789, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27996 p hg
    simpa only [d9789, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9789, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d9789, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27998 (p : Pattern) (guard : d9791 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9789 p = 1 := by simpa only [d9791, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27997 p hg
    simpa only [d9791, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9791, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d9791, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27999 (p : Pattern) (guard : d16438 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16438, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d16438, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9791 p = 1 := by simpa only [d16438, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27998 p hg
    simpa only [d16438, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
