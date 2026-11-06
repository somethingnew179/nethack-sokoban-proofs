import NetHack.Soko22Hazard87.Compare102
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare25750 (p : Pattern) (guard : d9457 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317 p = 1 := by simpa only [d9457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25634 p hg
    simpa only [d9457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9456 p = 1 := by simpa only [d9457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25749 p hg
    simpa only [d9457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25751 (p : Pattern) (guard : d9458 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9457 p = 1 := by simpa only [d9458, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25750 p hg
    simpa only [d9458, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9458, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d9458, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25752 (p : Pattern) (guard : d9460 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9458 p = 1 := by simpa only [d9460, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25751 p hg
    simpa only [d9460, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9460, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d9460, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25753 (p : Pattern) (guard : d16073 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16073, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d16073, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9460 p = 1 := by simpa only [d16073, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25752 p hg
    simpa only [d16073, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25754 (p : Pattern) (guard : d16074 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16073 p = 1 := by simpa only [d16074, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25753 p hg
    simpa only [d16074, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16074, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d16074, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25755 (p : Pattern) (guard : d16075 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d546 p = 1 := by simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25742 p hg
    simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16074 p = 1 := by simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25754 p hg
    simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25756 (p : Pattern) (guard : d9464 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d314 p = 1 := by simpa only [d9464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25631 p hg
    simpa only [d9464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9453 p = 1 := by simpa only [d9464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25746 p hg
    simpa only [d9464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25757 (p : Pattern) (guard : d9465 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9464 p = 1 := by simpa only [d9465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25756 p hg
    simpa only [d9465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d9465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25758 (p : Pattern) (guard : d9466 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9465 p = 1 := by simpa only [d9466, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25757 p hg
    simpa only [d9466, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9466, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d9466, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25759 (p : Pattern) (guard : d9467 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9466 p = 1 := by simpa only [d9467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25758 p hg
    simpa only [d9467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9456 p = 1 := by simpa only [d9467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25749 p hg
    simpa only [d9467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25760 (p : Pattern) (guard : d9468 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9467 p = 1 := by simpa only [d9468, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25759 p hg
    simpa only [d9468, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9468, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d9468, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25761 (p : Pattern) (guard : d9470 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9468 p = 1 := by simpa only [d9470, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25760 p hg
    simpa only [d9470, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9470, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d9470, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25762 (p : Pattern) (guard : d12748 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d12748, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d12748, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9470 p = 1 := by simpa only [d12748, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25761 p hg
    simpa only [d12748, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25763 (p : Pattern) (guard : d12749 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12748 p = 1 := by simpa only [d12749, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25762 p hg
    simpa only [d12749, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12749, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d12749, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25764 (p : Pattern) (guard : d16076 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12749 p = 1 := by simpa only [d16076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25763 p hg
    simpa only [d16076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12494 p = 1 := by simpa only [d16076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25647 p hg
    simpa only [d16076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25765 (p : Pattern) (guard : d16077 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16075 p = 1 := by simpa only [d16077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25755 p hg
    simpa only [d16077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16076 p = 1 := by simpa only [d16077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25764 p hg
    simpa only [d16077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25766 (p : Pattern) (guard : d16078 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16077 p = 1 := by simpa only [d16078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25765 p hg
    simpa only [d16078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15966 p = 1 := by simpa only [d16078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25649 p hg
    simpa only [d16078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25767 (p : Pattern) (guard : d16079 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16079, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d16079, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16078 p = 1 := by simpa only [d16079, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25766 p hg
    simpa only [d16079, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25768 (p : Pattern) (guard : d16080 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16080, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d16080, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16079 p = 1 := by simpa only [d16080, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25767 p hg
    simpa only [d16080, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25769 (p : Pattern) (guard : d16081 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d12495 p = 1 := by simpa only [d16081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25648 p hg
    simpa only [d16081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29 p = 1 := by simpa only [d16081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25488 p hg
    simpa only [d16081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25770 (p : Pattern) (guard : d16082 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d15966 p = 1 := by simpa only [d16082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25649 p hg
    simpa only [d16082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16081 p = 1 := by simpa only [d16082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25769 p hg
    simpa only [d16082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25771 (p : Pattern) (guard : d16083 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16083, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d16083, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16082 p = 1 := by simpa only [d16083, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25770 p hg
    simpa only [d16083, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25772 (p : Pattern) (guard : d16084 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16084, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d16084, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16083 p = 1 := by simpa only [d16084, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25771 p hg
    simpa only [d16084, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25773 (p : Pattern) (guard : d16085 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16080 p = 1 := by simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25768 p hg
    simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16084 p = 1 := by simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25772 p hg
    simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25774 (p : Pattern) (guard : d16086 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16085 p = 1 := by simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25773 p hg
    simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15970 p = 1 := by simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25653 p hg
    simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25775 (p : Pattern) (guard : d528 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d309 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25658 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25776 (p : Pattern) (guard : d529 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25775 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d310 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25659 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25777 (p : Pattern) (guard : d530 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d529 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25776 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d311 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25660 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25778 (p : Pattern) (guard : d531 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25777 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25779 (p : Pattern) (guard : d532 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d531 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25778 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25780 (p : Pattern) (guard : d533 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d532 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25779 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d314 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25663 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25781 (p : Pattern) (guard : d534 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25578 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25782 (p : Pattern) (guard : d535 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25659 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d534 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25781 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25783 (p : Pattern) (guard : d536 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d535 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25782 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25580 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25784 (p : Pattern) (guard : d537 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d536 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25783 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25785 (p : Pattern) (guard : d538 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d537 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25784 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25786 (p : Pattern) (guard : d539 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d538 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25785 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25583 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25787 (p : Pattern) (guard : d540 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d533 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25780 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25786 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25788 (p : Pattern) (guard : d541 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d540 p = 1 := by simpa only [d541, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25787 p hg
    simpa only [d541, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d541, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d541, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25789 (p : Pattern) (guard : d542 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d541 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25788 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25666 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25790 (p : Pattern) (guard : d543 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d542 p = 1 := by simpa only [d543, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25789 p hg
    simpa only [d543, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d543, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d543, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25791 (p : Pattern) (guard : d544 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d543 p = 1 := by simpa only [d544, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25790 p hg
    simpa only [d544, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d544, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d544, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25792 (p : Pattern) (guard : d545 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d545, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d545, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d544 p = 1 := by simpa only [d545, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25791 p hg
    simpa only [d545, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25793 (p : Pattern) (guard : d546 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d545 p = 1 := by simpa only [d546, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25792 p hg
    simpa only [d546, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d546, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d546, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25794 (p : Pattern) (guard : d5010 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d534 p = 1 := by simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25781 p hg
    simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16 p = 1 := by simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25501 p hg
    simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25795 (p : Pattern) (guard : d5011 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5010 p = 1 := by simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25794 p hg
    simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25502 p hg
    simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25796 (p : Pattern) (guard : d9452 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5011 p = 1 := by simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25795 p hg
    simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25797 (p : Pattern) (guard : d9453 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d9452 p = 1 := by simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25796 p hg
    simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25798 (p : Pattern) (guard : d9454 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d9453 p = 1 := by simpa only [d9454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25797 p hg
    simpa only [d9454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d9454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25505 p hg
    simpa only [d9454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25799 (p : Pattern) (guard : d9455 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9454 p = 1 := by simpa only [d9455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25798 p hg
    simpa only [d9455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d9455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25800 (p : Pattern) (guard : d9456 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9455 p = 1 := by simpa only [d9456, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25799 p hg
    simpa only [d9456, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9456, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d9456, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25801 (p : Pattern) (guard : d9457 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317 p = 1 := by simpa only [d9457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25666 p hg
    simpa only [d9457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9456 p = 1 := by simpa only [d9457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25800 p hg
    simpa only [d9457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25802 (p : Pattern) (guard : d9458 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9457 p = 1 := by simpa only [d9458, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25801 p hg
    simpa only [d9458, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9458, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d9458, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25803 (p : Pattern) (guard : d9460 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9458 p = 1 := by simpa only [d9460, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25802 p hg
    simpa only [d9460, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9460, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d9460, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25804 (p : Pattern) (guard : d16073 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16073, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d16073, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9460 p = 1 := by simpa only [d16073, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25803 p hg
    simpa only [d16073, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25805 (p : Pattern) (guard : d16074 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16073 p = 1 := by simpa only [d16074, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25804 p hg
    simpa only [d16074, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16074, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d16074, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25806 (p : Pattern) (guard : d16075 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d546 p = 1 := by simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25793 p hg
    simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16074 p = 1 := by simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25805 p hg
    simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25807 (p : Pattern) (guard : d9464 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d314 p = 1 := by simpa only [d9464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25663 p hg
    simpa only [d9464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9453 p = 1 := by simpa only [d9464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25797 p hg
    simpa only [d9464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25808 (p : Pattern) (guard : d9465 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9464 p = 1 := by simpa only [d9465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25807 p hg
    simpa only [d9465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d9465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25809 (p : Pattern) (guard : d9466 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9465 p = 1 := by simpa only [d9466, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25808 p hg
    simpa only [d9466, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9466, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d9466, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25810 (p : Pattern) (guard : d9467 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9466 p = 1 := by simpa only [d9467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25809 p hg
    simpa only [d9467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9456 p = 1 := by simpa only [d9467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25800 p hg
    simpa only [d9467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25811 (p : Pattern) (guard : d9468 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9467 p = 1 := by simpa only [d9468, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25810 p hg
    simpa only [d9468, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9468, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d9468, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25812 (p : Pattern) (guard : d9470 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9468 p = 1 := by simpa only [d9470, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25811 p hg
    simpa only [d9470, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9470, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d9470, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25813 (p : Pattern) (guard : d12748 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d12748, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d12748, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9470 p = 1 := by simpa only [d12748, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25812 p hg
    simpa only [d12748, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25814 (p : Pattern) (guard : d12749 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12748 p = 1 := by simpa only [d12749, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25813 p hg
    simpa only [d12749, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12749, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d12749, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25815 (p : Pattern) (guard : d16076 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12749 p = 1 := by simpa only [d16076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25814 p hg
    simpa only [d16076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12494 p = 1 := by simpa only [d16076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25679 p hg
    simpa only [d16076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25816 (p : Pattern) (guard : d16077 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16075 p = 1 := by simpa only [d16077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25806 p hg
    simpa only [d16077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16076 p = 1 := by simpa only [d16077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25815 p hg
    simpa only [d16077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25817 (p : Pattern) (guard : d16078 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16077 p = 1 := by simpa only [d16078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25816 p hg
    simpa only [d16078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15966 p = 1 := by simpa only [d16078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25681 p hg
    simpa only [d16078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25818 (p : Pattern) (guard : d18729 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d16078 p = 1 := by simpa only [d18729, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25817 p hg
    simpa only [d18729, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18729, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d18729, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25819 (p : Pattern) (guard : d18730 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d18730, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d18730, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18729 p = 1 := by simpa only [d18730, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25818 p hg
    simpa only [d18730, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25820 (p : Pattern) (guard : d16081 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d12495 p = 1 := by simpa only [d16081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25680 p hg
    simpa only [d16081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29 p = 1 := by simpa only [d16081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25519 p hg
    simpa only [d16081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25821 (p : Pattern) (guard : d16082 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d15966 p = 1 := by simpa only [d16082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25681 p hg
    simpa only [d16082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16081 p = 1 := by simpa only [d16082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25820 p hg
    simpa only [d16082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25822 (p : Pattern) (guard : d18731 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d16082 p = 1 := by simpa only [d18731, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25821 p hg
    simpa only [d18731, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18731, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d18731, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25823 (p : Pattern) (guard : d18732 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d18732, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d18732, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18731 p = 1 := by simpa only [d18732, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25822 p hg
    simpa only [d18732, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25824 (p : Pattern) (guard : d18733 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d18730 p = 1 := by simpa only [d18733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25819 p hg
    simpa only [d18733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18732 p = 1 := by simpa only [d18733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25823 p hg
    simpa only [d18733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25825 (p : Pattern) (guard : d18734 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d18733 p = 1 := by simpa only [d18734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25824 p hg
    simpa only [d18734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18647 p = 1 := by simpa only [d18734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25685 p hg
    simpa only [d18734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25826 (p : Pattern) (guard : d187963 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16086 p = 1 := by simpa only [d187963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25774 p hg
    simpa only [d187963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18734 p = 1 := by simpa only [d187963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25825 p hg
    simpa only [d187963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25827 (p : Pattern) (guard : d187964 p = 1) : d48705 p ≤ (-1 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d187963 p = 1 := by simpa only [d187964, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25826 p hg
    simpa only [d187964, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187964, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25527 p hg
    simpa only [d187964, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25828 (p : Pattern) (guard : d187965 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187965, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25461 p hg
    simpa only [d187965, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187964 p = 1 := by simpa only [d187965, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25827 p hg
    simpa only [d187965, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25829 (p : Pattern) (guard : d475 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25572 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25830 (p : Pattern) (guard : d16035 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d15970 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25653 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d475 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25829 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25831 (p : Pattern) (guard : d18740 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d18582 p = 1 := by simpa only [d18740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25596 p hg
    simpa only [d18740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d18740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25832 (p : Pattern) (guard : d18741 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d18647 p = 1 := by simpa only [d18741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25685 p hg
    simpa only [d18741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18740 p = 1 := by simpa only [d18741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25831 p hg
    simpa only [d18741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25833 (p : Pattern) (guard : d187966 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16035 p = 1 := by simpa only [d187966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25830 p hg
    simpa only [d187966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18741 p = 1 := by simpa only [d187966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25832 p hg
    simpa only [d187966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25834 (p : Pattern) (guard : d187967 p = 1) : d48705 p ≤ (-1 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d187966 p = 1 := by simpa only [d187967, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25833 p hg
    simpa only [d187967, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187967, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25527 p hg
    simpa only [d187967, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25835 (p : Pattern) (guard : d187968 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187968, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25461 p hg
    simpa only [d187968, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187967 p = 1 := by simpa only [d187968, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25834 p hg
    simpa only [d187968, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25836 (p : Pattern) (guard : d187969 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d187965 p = 1 := by simpa only [d187969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d187969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187968 p = 1 := by simpa only [d187969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25835 p hg
    simpa only [d187969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25837 (p : Pattern) (guard : d187970 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d187969 p = 1 := by simpa only [d187970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25836 p hg
    simpa only [d187970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25838 (p : Pattern) (guard : d187971 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d187970 p = 1 := by simpa only [d187971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25837 p hg
    simpa only [d187971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25839 (p : Pattern) (guard : d187972 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d187971 p = 1 := by simpa only [d187972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25838 p hg
    simpa only [d187972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25840 (p : Pattern) (guard : d480 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d475 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25829 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25841 (p : Pattern) (guard : d18750 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d18740 p = 1 := by simpa only [d18750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25831 p hg
    simpa only [d18750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d18750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25842 (p : Pattern) (guard : d187973 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d480 p = 1 := by simpa only [d187973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25840 p hg
    simpa only [d187973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18750 p = 1 := by simpa only [d187973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25841 p hg
    simpa only [d187973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25843 (p : Pattern) (guard : d187974 p = 1) : d48705 p ≤ (-1 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d187973 p = 1 := by simpa only [d187974, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25842 p hg
    simpa only [d187974, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187974, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25527 p hg
    simpa only [d187974, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25844 (p : Pattern) (guard : d187975 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187975, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25461 p hg
    simpa only [d187975, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187974 p = 1 := by simpa only [d187975, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25843 p hg
    simpa only [d187975, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25845 (p : Pattern) (guard : d187976 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d187968 p = 1 := by simpa only [d187976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25835 p hg
    simpa only [d187976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187975 p = 1 := by simpa only [d187976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25844 p hg
    simpa only [d187976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25846 (p : Pattern) (guard : d187977 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d187976 p = 1 := by simpa only [d187977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25845 p hg
    simpa only [d187977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25847 (p : Pattern) (guard : d187978 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d187977 p = 1 := by simpa only [d187978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25846 p hg
    simpa only [d187978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25848 (p : Pattern) (guard : d187979 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d187978 p = 1 := by simpa only [d187979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25847 p hg
    simpa only [d187979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25849 (p : Pattern) (guard : d187980 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d187972 p = 1 := by simpa only [d187980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25839 p hg
    simpa only [d187980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187979 p = 1 := by simpa only [d187980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25848 p hg
    simpa only [d187980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25850 (p : Pattern) (guard : d187981 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d187980 p = 1 := by simpa only [d187981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25849 p hg
    simpa only [d187981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25851 (p : Pattern) (guard : d187982 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d187968 p = 1 := by simpa only [d187982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25835 p hg
    simpa only [d187982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25852 (p : Pattern) (guard : d187983 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d187982 p = 1 := by simpa only [d187983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25851 p hg
    simpa only [d187983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25853 (p : Pattern) (guard : d187984 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d187983 p = 1 := by simpa only [d187984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25852 p hg
    simpa only [d187984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25854 (p : Pattern) (guard : d187985 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d187984 p = 1 := by simpa only [d187985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25853 p hg
    simpa only [d187985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25855 (p : Pattern) (guard : d187986 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d187985 p = 1 := by simpa only [d187986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25854 p hg
    simpa only [d187986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25856 (p : Pattern) (guard : d187987 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d187986 p = 1 := by simpa only [d187987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25855 p hg
    simpa only [d187987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25857 (p : Pattern) (guard : d187988 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 89 with
  | false =>
    have hg : d187981 p = 1 := by simpa only [d187988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25850 p hg
    simpa only [d187988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187987 p = 1 := by simpa only [d187988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25856 p hg
    simpa only [d187988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25858 (p : Pattern) (guard : d187989 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187988 p = 1 := by simpa only [d187989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25857 p hg
    simpa only [d187989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25859 (p : Pattern) (guard : d187990 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187989 p = 1 := by simpa only [d187990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25858 p hg
    simpa only [d187990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25860 (p : Pattern) (guard : d187991 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187991, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25459 p hg
    simpa only [d187991, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187990 p = 1 := by simpa only [d187991, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25859 p hg
    simpa only [d187991, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25861 (p : Pattern) (guard : d187992 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d187992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187991 p = 1 := by simpa only [d187992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25860 p hg
    simpa only [d187992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25862 (p : Pattern) (guard : d187993 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d187975 p = 1 := by simpa only [d187993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25844 p hg
    simpa only [d187993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25863 (p : Pattern) (guard : d187994 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d187993 p = 1 := by simpa only [d187994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25862 p hg
    simpa only [d187994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25864 (p : Pattern) (guard : d187995 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d187994 p = 1 := by simpa only [d187995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25863 p hg
    simpa only [d187995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25865 (p : Pattern) (guard : d187996 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d187995 p = 1 := by simpa only [d187996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25864 p hg
    simpa only [d187996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25866 (p : Pattern) (guard : d187997 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d187996 p = 1 := by simpa only [d187997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25865 p hg
    simpa only [d187997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25867 (p : Pattern) (guard : d187998 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d187998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187997 p = 1 := by simpa only [d187998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25866 p hg
    simpa only [d187998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25868 (p : Pattern) (guard : d187999 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 89 with
  | false =>
    have hg : d187998 p = 1 := by simpa only [d187999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25867 p hg
    simpa only [d187999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d187999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d187999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25869 (p : Pattern) (guard : d188000 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d187999 p = 1 := by simpa only [d188000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25868 p hg
    simpa only [d188000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25870 (p : Pattern) (guard : d188001 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188000 p = 1 := by simpa only [d188001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25869 p hg
    simpa only [d188001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25871 (p : Pattern) (guard : d188002 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188002, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25459 p hg
    simpa only [d188002, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188001 p = 1 := by simpa only [d188002, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25870 p hg
    simpa only [d188002, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25872 (p : Pattern) (guard : d188003 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d188003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188002 p = 1 := by simpa only [d188003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25871 p hg
    simpa only [d188003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25873 (p : Pattern) (guard : d188004 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 69 with
  | false =>
    have hg : d187992 p = 1 := by simpa only [d188004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25861 p hg
    simpa only [d188004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188003 p = 1 := by simpa only [d188004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25872 p hg
    simpa only [d188004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25874 (p : Pattern) (guard : d188005 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 51 with
  | false =>
    have hg : d188004 p = 1 := by simpa only [d188005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25873 p hg
    simpa only [d188005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d188005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25875 (p : Pattern) (guard : d188006 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 50 with
  | false =>
    have hg : d188005 p = 1 := by simpa only [d188006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25874 p hg
    simpa only [d188006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d188006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25876 (p : Pattern) (guard : d188007 p = 1) : d48748 p ≤ (-1 : Int) + d188517 p := by
  cases selected : p 49 with
  | false =>
    have hg : d188006 p = 1 := by simpa only [d188007, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25875 p hg
    simpa only [d188007, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188007, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25544 p hg
    simpa only [d188007, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25877 (p : Pattern) (guard : d188008 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188008, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25457 p hg
    simpa only [d188008, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188007 p = 1 := by simpa only [d188008, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25876 p hg
    simpa only [d188008, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25878 (p : Pattern) (guard : d188009 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188008 p = 1 := by simpa only [d188009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25877 p hg
    simpa only [d188009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25879 (p : Pattern) (guard : d188010 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188009 p = 1 := by simpa only [d188010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25878 p hg
    simpa only [d188010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25880 (p : Pattern) (guard : d188011 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188010 p = 1 := by simpa only [d188011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25879 p hg
    simpa only [d188011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25881 (p : Pattern) (guard : d188012 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188011 p = 1 := by simpa only [d188012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25880 p hg
    simpa only [d188012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25882 (p : Pattern) (guard : d188013 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188012 p = 1 := by simpa only [d188013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25881 p hg
    simpa only [d188013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25883 (p : Pattern) (guard : d188014 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188013 p = 1 := by simpa only [d188014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25882 p hg
    simpa only [d188014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25884 (p : Pattern) (guard : d188015 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d187962 p = 1 := by simpa only [d188015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25723 p hg
    simpa only [d188015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188014 p = 1 := by simpa only [d188015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25883 p hg
    simpa only [d188015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25885 (p : Pattern) (guard : d820 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d528 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25724 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25886 (p : Pattern) (guard : d821 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25885 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d529 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25725 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25887 (p : Pattern) (guard : d822 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d821 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25886 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25888 (p : Pattern) (guard : d823 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d822 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25887 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25889 (p : Pattern) (guard : d824 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25888 p hg
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d532 p = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25728 p hg
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25890 (p : Pattern) (guard : d825 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25626 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25891 (p : Pattern) (guard : d826 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25724 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d825 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25890 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25892 (p : Pattern) (guard : d827 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25891 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d535 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25731 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25893 (p : Pattern) (guard : d828 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d827 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25892 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25894 (p : Pattern) (guard : d829 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25893 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25895 (p : Pattern) (guard : d830 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25894 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d538 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25734 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25896 (p : Pattern) (guard : d831 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d824 p = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25889 p hg
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25895 p hg
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25897 (p : Pattern) (guard : d832 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d831 p = 1 := by simpa only [d832, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25896 p hg
    simpa only [d832, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d832, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d832, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25898 (p : Pattern) (guard : d833 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d832 p = 1 := by simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25897 p hg
    simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d541 p = 1 := by simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25737 p hg
    simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25899 (p : Pattern) (guard : d834 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d833 p = 1 := by simpa only [d834, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25898 p hg
    simpa only [d834, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d834, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d834, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25900 (p : Pattern) (guard : d835 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d834 p = 1 := by simpa only [d835, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25899 p hg
    simpa only [d835, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d835, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d835, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25901 (p : Pattern) (guard : d836 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d836, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d836, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d835 p = 1 := by simpa only [d836, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25900 p hg
    simpa only [d836, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25902 (p : Pattern) (guard : d837 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d836 p = 1 := by simpa only [d837, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25901 p hg
    simpa only [d837, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d837, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d837, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25903 (p : Pattern) (guard : d5121 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d825 p = 1 := by simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25890 p hg
    simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25904 (p : Pattern) (guard : d308 p = 1) : d2 p ≤ (-1 : Int) + d4 p := by
  have ha := bounds2 p
  have hb := bounds4 p
  omega
theorem compare25905 (p : Pattern) (guard : d1519 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 246 with
  | false =>
    have hg : d308 p = 1 := by simpa only [d1519, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25904 p hg
    simpa only [d1519, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1519, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25466 p hg
    simpa only [d1519, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25906 (p : Pattern) (guard : d1531 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25905 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25907 (p : Pattern) (guard : d9579 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d9579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25906 p hg
    simpa only [d9579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16 p = 1 := by simpa only [d9579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25469 p hg
    simpa only [d9579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25908 (p : Pattern) (guard : d9580 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5121 p = 1 := by simpa only [d9580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25903 p hg
    simpa only [d9580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9579 p = 1 := by simpa only [d9580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25907 p hg
    simpa only [d9580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25909 (p : Pattern) (guard : d9581 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d9580 p = 1 := by simpa only [d9581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25908 p hg
    simpa only [d9581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d9581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25910 (p : Pattern) (guard : d9582 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d9581 p = 1 := by simpa only [d9582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25909 p hg
    simpa only [d9582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d9582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25911 (p : Pattern) (guard : d9583 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d9582 p = 1 := by simpa only [d9583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25910 p hg
    simpa only [d9583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9453 p = 1 := by simpa only [d9583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25746 p hg
    simpa only [d9583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25912 (p : Pattern) (guard : d9584 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9583 p = 1 := by simpa only [d9584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25911 p hg
    simpa only [d9584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d9584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25913 (p : Pattern) (guard : d9585 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9584 p = 1 := by simpa only [d9585, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25912 p hg
    simpa only [d9585, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9585, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d9585, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25914 (p : Pattern) (guard : d9586 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d541 p = 1 := by simpa only [d9586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25737 p hg
    simpa only [d9586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9585 p = 1 := by simpa only [d9586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25913 p hg
    simpa only [d9586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25915 (p : Pattern) (guard : d9587 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9586 p = 1 := by simpa only [d9587, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25914 p hg
    simpa only [d9587, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9587, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d9587, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25916 (p : Pattern) (guard : d9589 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9587 p = 1 := by simpa only [d9589, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25915 p hg
    simpa only [d9589, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9589, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d9589, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25917 (p : Pattern) (guard : d16270 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16270, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d16270, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9589 p = 1 := by simpa only [d16270, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25916 p hg
    simpa only [d16270, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25918 (p : Pattern) (guard : d16271 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16270 p = 1 := by simpa only [d16271, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25917 p hg
    simpa only [d16271, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16271, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d16271, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25919 (p : Pattern) (guard : d16272 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d837 p = 1 := by simpa only [d16272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25902 p hg
    simpa only [d16272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16271 p = 1 := by simpa only [d16272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25918 p hg
    simpa only [d16272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25920 (p : Pattern) (guard : d9593 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d532 p = 1 := by simpa only [d9593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25728 p hg
    simpa only [d9593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9582 p = 1 := by simpa only [d9593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25910 p hg
    simpa only [d9593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25921 (p : Pattern) (guard : d9594 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9593 p = 1 := by simpa only [d9594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25920 p hg
    simpa only [d9594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d9594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25922 (p : Pattern) (guard : d9595 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9594 p = 1 := by simpa only [d9595, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25921 p hg
    simpa only [d9595, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9595, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d9595, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25923 (p : Pattern) (guard : d9596 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9595 p = 1 := by simpa only [d9596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25922 p hg
    simpa only [d9596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9585 p = 1 := by simpa only [d9596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25913 p hg
    simpa only [d9596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25924 (p : Pattern) (guard : d9597 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9596 p = 1 := by simpa only [d9597, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25923 p hg
    simpa only [d9597, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9597, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d9597, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25925 (p : Pattern) (guard : d9599 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9597 p = 1 := by simpa only [d9599, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25924 p hg
    simpa only [d9599, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9599, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d9599, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25926 (p : Pattern) (guard : d14529 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14529, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d14529, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9599 p = 1 := by simpa only [d14529, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25925 p hg
    simpa only [d14529, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25927 (p : Pattern) (guard : d14530 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14529 p = 1 := by simpa only [d14530, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25926 p hg
    simpa only [d14530, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14530, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d14530, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25928 (p : Pattern) (guard : d16273 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14530 p = 1 := by simpa only [d16273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25927 p hg
    simpa only [d16273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12749 p = 1 := by simpa only [d16273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25763 p hg
    simpa only [d16273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25929 (p : Pattern) (guard : d16274 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16272 p = 1 := by simpa only [d16274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25919 p hg
    simpa only [d16274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16273 p = 1 := by simpa only [d16274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25928 p hg
    simpa only [d16274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25930 (p : Pattern) (guard : d750 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25562 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25478 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25931 (p : Pattern) (guard : d751 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d750 p = 1 := by simpa only [d751, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25930 p hg
    simpa only [d751, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d751, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d751, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25932 (p : Pattern) (guard : d752 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d751 p = 1 := by simpa only [d752, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25931 p hg
    simpa only [d752, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d752, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d752, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25933 (p : Pattern) (guard : d753 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d753, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d753, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d752 p = 1 := by simpa only [d753, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25932 p hg
    simpa only [d753, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25934 (p : Pattern) (guard : d754 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25933 p hg
    simpa only [d754, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d754, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25935 (p : Pattern) (guard : d12750 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12749 p = 1 := by simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25763 p hg
    simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25934 p hg
    simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25936 (p : Pattern) (guard : d16227 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16075 p = 1 := by simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25755 p hg
    simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12750 p = 1 := by simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25935 p hg
    simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25937 (p : Pattern) (guard : d16275 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16274 p = 1 := by simpa only [d16275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25929 p hg
    simpa only [d16275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16227 p = 1 := by simpa only [d16275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25936 p hg
    simpa only [d16275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25938 (p : Pattern) (guard : d16276 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16276, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d16276, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16275 p = 1 := by simpa only [d16276, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25937 p hg
    simpa only [d16276, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25939 (p : Pattern) (guard : d16277 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16277, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d16277, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16276 p = 1 := by simpa only [d16277, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25938 p hg
    simpa only [d16277, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25940 (p : Pattern) (guard : d757 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d754 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25934 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25941 (p : Pattern) (guard : d16278 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d12750 p = 1 := by simpa only [d16278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25935 p hg
    simpa only [d16278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d757 p = 1 := by simpa only [d16278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25940 p hg
    simpa only [d16278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25942 (p : Pattern) (guard : d16279 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16227 p = 1 := by simpa only [d16279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25936 p hg
    simpa only [d16279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16278 p = 1 := by simpa only [d16279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25941 p hg
    simpa only [d16279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25943 (p : Pattern) (guard : d16280 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16280, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d16280, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16279 p = 1 := by simpa only [d16280, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25942 p hg
    simpa only [d16280, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25944 (p : Pattern) (guard : d16281 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16281, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d16281, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16280 p = 1 := by simpa only [d16281, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25943 p hg
    simpa only [d16281, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25945 (p : Pattern) (guard : d16282 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16277 p = 1 := by simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25939 p hg
    simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16281 p = 1 := by simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25944 p hg
    simpa only [d16282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25946 (p : Pattern) (guard : d755 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25639 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25934 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25947 (p : Pattern) (guard : d758 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d755 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25946 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d757 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25940 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25948 (p : Pattern) (guard : d16228 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16227 p = 1 := by simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25936 p hg
    simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25947 p hg
    simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25949 (p : Pattern) (guard : d16229 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16229, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d16229, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16228 p = 1 := by simpa only [d16229, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25948 p hg
    simpa only [d16229, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25950 (p : Pattern) (guard : d16230 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16230, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d16230, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16229 p = 1 := by simpa only [d16230, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25949 p hg
    simpa only [d16230, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25951 (p : Pattern) (guard : d762 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25940 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25952 (p : Pattern) (guard : d763 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25947 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d762 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25951 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25953 (p : Pattern) (guard : d764 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d764, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d764, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d763 p = 1 := by simpa only [d764, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25952 p hg
    simpa only [d764, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25954 (p : Pattern) (guard : d765 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d765, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d765, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d764 p = 1 := by simpa only [d765, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25953 p hg
    simpa only [d765, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25955 (p : Pattern) (guard : d16231 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16230 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25950 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25954 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25956 (p : Pattern) (guard : d16283 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16282 p = 1 := by simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25945 p hg
    simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16231 p = 1 := by simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25955 p hg
    simpa only [d16283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25957 (p : Pattern) (guard : d820 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d528 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25775 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25958 (p : Pattern) (guard : d821 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25957 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d529 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25776 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25959 (p : Pattern) (guard : d822 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d821 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25958 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25960 (p : Pattern) (guard : d823 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d822 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25959 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25961 (p : Pattern) (guard : d824 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25960 p hg
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d532 p = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25779 p hg
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25962 (p : Pattern) (guard : d825 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25658 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25963 (p : Pattern) (guard : d826 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25775 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d825 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25962 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25964 (p : Pattern) (guard : d827 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25963 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d535 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25782 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25965 (p : Pattern) (guard : d828 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d827 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25964 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25966 (p : Pattern) (guard : d829 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25965 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25967 (p : Pattern) (guard : d830 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25966 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d538 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25785 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25968 (p : Pattern) (guard : d831 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d824 p = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25961 p hg
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25967 p hg
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25969 (p : Pattern) (guard : d832 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d831 p = 1 := by simpa only [d832, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25968 p hg
    simpa only [d832, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d832, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d832, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25970 (p : Pattern) (guard : d833 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d832 p = 1 := by simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25969 p hg
    simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d541 p = 1 := by simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25788 p hg
    simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25971 (p : Pattern) (guard : d834 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d833 p = 1 := by simpa only [d834, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25970 p hg
    simpa only [d834, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d834, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d834, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25972 (p : Pattern) (guard : d835 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d834 p = 1 := by simpa only [d835, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25971 p hg
    simpa only [d835, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d835, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d835, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25973 (p : Pattern) (guard : d836 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d836, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d836, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d835 p = 1 := by simpa only [d836, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25972 p hg
    simpa only [d836, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25974 (p : Pattern) (guard : d837 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d836 p = 1 := by simpa only [d837, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25973 p hg
    simpa only [d837, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d837, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d837, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25975 (p : Pattern) (guard : d5121 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d825 p = 1 := by simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25962 p hg
    simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25976 (p : Pattern) (guard : d308 p = 1) : d0 p ≤ (-1 : Int) + d2 p := by
  have ha := bounds0 p
  have hb := bounds2 p
  omega
theorem compare25977 (p : Pattern) (guard : d1519 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 246 with
  | false =>
    have hg : d308 p = 1 := by simpa only [d1519, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25976 p hg
    simpa only [d1519, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1519, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25498 p hg
    simpa only [d1519, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25978 (p : Pattern) (guard : d1531 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25977 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25979 (p : Pattern) (guard : d9579 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d9579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25978 p hg
    simpa only [d9579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16 p = 1 := by simpa only [d9579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25501 p hg
    simpa only [d9579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25980 (p : Pattern) (guard : d9580 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5121 p = 1 := by simpa only [d9580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25975 p hg
    simpa only [d9580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9579 p = 1 := by simpa only [d9580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25979 p hg
    simpa only [d9580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25981 (p : Pattern) (guard : d9581 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d9580 p = 1 := by simpa only [d9581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25980 p hg
    simpa only [d9581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d9581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25982 (p : Pattern) (guard : d9582 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d9581 p = 1 := by simpa only [d9582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25981 p hg
    simpa only [d9582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d9582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25983 (p : Pattern) (guard : d9583 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d9582 p = 1 := by simpa only [d9583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25982 p hg
    simpa only [d9583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9453 p = 1 := by simpa only [d9583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25797 p hg
    simpa only [d9583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25984 (p : Pattern) (guard : d9584 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9583 p = 1 := by simpa only [d9584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25983 p hg
    simpa only [d9584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d9584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25985 (p : Pattern) (guard : d9585 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9584 p = 1 := by simpa only [d9585, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25984 p hg
    simpa only [d9585, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9585, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d9585, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25986 (p : Pattern) (guard : d9586 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d541 p = 1 := by simpa only [d9586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25788 p hg
    simpa only [d9586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9585 p = 1 := by simpa only [d9586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25985 p hg
    simpa only [d9586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25987 (p : Pattern) (guard : d9587 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9586 p = 1 := by simpa only [d9587, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25986 p hg
    simpa only [d9587, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9587, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d9587, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25988 (p : Pattern) (guard : d9589 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9587 p = 1 := by simpa only [d9589, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25987 p hg
    simpa only [d9589, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9589, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d9589, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25989 (p : Pattern) (guard : d16270 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16270, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d16270, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9589 p = 1 := by simpa only [d16270, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25988 p hg
    simpa only [d16270, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25990 (p : Pattern) (guard : d16271 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16270 p = 1 := by simpa only [d16271, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25989 p hg
    simpa only [d16271, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16271, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d16271, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25991 (p : Pattern) (guard : d16272 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d837 p = 1 := by simpa only [d16272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25974 p hg
    simpa only [d16272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16271 p = 1 := by simpa only [d16272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25990 p hg
    simpa only [d16272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25992 (p : Pattern) (guard : d9593 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d532 p = 1 := by simpa only [d9593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25779 p hg
    simpa only [d9593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9582 p = 1 := by simpa only [d9593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25982 p hg
    simpa only [d9593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25993 (p : Pattern) (guard : d9594 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9593 p = 1 := by simpa only [d9594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25992 p hg
    simpa only [d9594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d9594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25994 (p : Pattern) (guard : d9595 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9594 p = 1 := by simpa only [d9595, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25993 p hg
    simpa only [d9595, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9595, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d9595, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25995 (p : Pattern) (guard : d9596 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9595 p = 1 := by simpa only [d9596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25994 p hg
    simpa only [d9596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9585 p = 1 := by simpa only [d9596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25985 p hg
    simpa only [d9596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25996 (p : Pattern) (guard : d9597 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9596 p = 1 := by simpa only [d9597, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25995 p hg
    simpa only [d9597, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9597, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d9597, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25997 (p : Pattern) (guard : d9599 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9597 p = 1 := by simpa only [d9599, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25996 p hg
    simpa only [d9599, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9599, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d9599, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25998 (p : Pattern) (guard : d14529 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14529, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d14529, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9599 p = 1 := by simpa only [d14529, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25997 p hg
    simpa only [d14529, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25999 (p : Pattern) (guard : d14530 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14529 p = 1 := by simpa only [d14530, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25998 p hg
    simpa only [d14530, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14530, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d14530, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
