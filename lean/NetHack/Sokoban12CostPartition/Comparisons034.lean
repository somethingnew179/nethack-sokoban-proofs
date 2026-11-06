/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons033
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare4760 (p : Pattern) (guard : d854 p = 1) : d548 p ≤ (2 : Int) + d239 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d548, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4744 p hg
    simpa only [d548, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d548, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4759 p hg
    simpa only [d548, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4761 (p : Pattern) (guard : d854 p = 1) : d549 p ≤ (2 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d549, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4735 p hg
    simpa only [d549, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d549, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4733 p hg
    simpa only [d549, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4762 (p : Pattern) (guard : d854 p = 1) : d550 p ≤ (2 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d550, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4743 p hg
    simpa only [d550, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d550, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4751 p hg
    simpa only [d550, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4763 (p : Pattern) (guard : d854 p = 1) : d551 p ≤ (2 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d551, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4761 p hg
    simpa only [d551, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d551, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4762 p hg
    simpa only [d551, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4764 (p : Pattern) (guard : d854 p = 1) : d552 p ≤ (2 : Int) + d181 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d552, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4749 p hg
    simpa only [d552, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d552, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4733 p hg
    simpa only [d552, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4765 (p : Pattern) (guard : d854 p = 1) : d553 p ≤ (2 : Int) + d240 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d553, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4757 p hg
    simpa only [d553, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d553, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4751 p hg
    simpa only [d553, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4766 (p : Pattern) (guard : d854 p = 1) : d554 p ≤ (2 : Int) + d241 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d554, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4764 p hg
    simpa only [d554, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d554, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4765 p hg
    simpa only [d554, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4767 (p : Pattern) (guard : d854 p = 1) : d555 p ≤ (2 : Int) + d242 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d555, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4763 p hg
    simpa only [d555, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d555, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4766 p hg
    simpa only [d555, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4768 (p : Pattern) (guard : d854 p = 1) : d556 p ≤ (2 : Int) + d243 p := by
  cases selected : p 133 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d556, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4760 p hg
    simpa only [d556, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d556, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4767 p hg
    simpa only [d556, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4769 (p : Pattern) (guard : d854 p = 1) : d557 p ≤ (2 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d557, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4733 p hg
    simpa only [d557, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d557, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4751 p hg
    simpa only [d557, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4770 (p : Pattern) (guard : d854 p = 1) : d558 p ≤ (2 : Int) + d244 p := by
  cases selected : p 133 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d558, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4767 p hg
    simpa only [d558, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d558, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4769 p hg
    simpa only [d558, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4771 (p : Pattern) (guard : d854 p = 1) : d559 p ≤ (2 : Int) + d245 p := by
  cases selected : p 132 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d559, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4768 p hg
    simpa only [d559, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d559, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4770 p hg
    simpa only [d559, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4772 (p : Pattern) (guard : d854 p = 1) : d560 p ≤ (2 : Int) + d137 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d560, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4746 p hg
    simpa only [d560, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d560, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4733 p hg
    simpa only [d560, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4773 (p : Pattern) (guard : d854 p = 1) : d561 p ≤ (2 : Int) + d139 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d561, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4747 p hg
    simpa only [d561, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d561, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4772 p hg
    simpa only [d561, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4774 (p : Pattern) (guard : d854 p = 1) : d562 p ≤ (2 : Int) + d153 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d562, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4735 p hg
    simpa only [d562, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d562, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4773 p hg
    simpa only [d562, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4775 (p : Pattern) (guard : d854 p = 1) : d563 p ≤ (2 : Int) + d186 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d563, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4735 p hg
    simpa only [d563, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d563, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4774 p hg
    simpa only [d563, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4776 (p : Pattern) (guard : d854 p = 1) : d564 p ≤ (2 : Int) + d143 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d564, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4753 p hg
    simpa only [d564, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d564, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4740 p hg
    simpa only [d564, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4777 (p : Pattern) (guard : d854 p = 1) : d565 p ≤ (2 : Int) + d144 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d565, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4772 p hg
    simpa only [d565, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d565, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4776 p hg
    simpa only [d565, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4778 (p : Pattern) (guard : d854 p = 1) : d566 p ≤ (2 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d566, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4755 p hg
    simpa only [d566, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d566, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4777 p hg
    simpa only [d566, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4779 (p : Pattern) (guard : d854 p = 1) : d567 p ≤ (2 : Int) + d155 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d567, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4743 p hg
    simpa only [d567, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d567, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4778 p hg
    simpa only [d567, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4780 (p : Pattern) (guard : d854 p = 1) : d568 p ≤ (2 : Int) + d246 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d568, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4743 p hg
    simpa only [d568, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d568, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4779 p hg
    simpa only [d568, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4781 (p : Pattern) (guard : d854 p = 1) : d569 p ≤ (2 : Int) + d247 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d569, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4775 p hg
    simpa only [d569, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d569, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4780 p hg
    simpa only [d569, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4782 (p : Pattern) (guard : d854 p = 1) : d570 p ≤ (2 : Int) + d248 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d570, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4781 p hg
    simpa only [d570, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d570, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4769 p hg
    simpa only [d570, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4783 (p : Pattern) (guard : d854 p = 1) : d571 p ≤ (2 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d571, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4731 p hg
    simpa only [d571, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d571, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4772 p hg
    simpa only [d571, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4784 (p : Pattern) (guard : d854 p = 1) : d572 p ≤ (2 : Int) + d140 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d572, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4783 p hg
    simpa only [d572, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d572, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4773 p hg
    simpa only [d572, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4785 (p : Pattern) (guard : d854 p = 1) : d573 p ≤ (2 : Int) + d188 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d573, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4784 p hg
    simpa only [d573, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d573, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4733 p hg
    simpa only [d573, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4786 (p : Pattern) (guard : d854 p = 1) : d574 p ≤ (2 : Int) + d145 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d574, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4738 p hg
    simpa only [d574, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d574, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4777 p hg
    simpa only [d574, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4787 (p : Pattern) (guard : d854 p = 1) : d575 p ≤ (2 : Int) + d147 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d575, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4786 p hg
    simpa only [d575, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d575, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4778 p hg
    simpa only [d575, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4788 (p : Pattern) (guard : d854 p = 1) : d576 p ≤ (2 : Int) + d249 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d576, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4787 p hg
    simpa only [d576, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d576, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4751 p hg
    simpa only [d576, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4789 (p : Pattern) (guard : d854 p = 1) : d577 p ≤ (2 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d577, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4785 p hg
    simpa only [d577, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d577, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4788 p hg
    simpa only [d577, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4790 (p : Pattern) (guard : d854 p = 1) : d578 p ≤ (2 : Int) + d251 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d578, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4789 p hg
    simpa only [d578, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d578, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4769 p hg
    simpa only [d578, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4791 (p : Pattern) (guard : d854 p = 1) : d579 p ≤ (2 : Int) + d252 p := by
  cases selected : p 133 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d579, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4782 p hg
    simpa only [d579, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d579, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4790 p hg
    simpa only [d579, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4792 (p : Pattern) (guard : d854 p = 1) : d580 p ≤ (2 : Int) + d191 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d580, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4774 p hg
    simpa only [d580, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d580, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4733 p hg
    simpa only [d580, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4793 (p : Pattern) (guard : d854 p = 1) : d581 p ≤ (2 : Int) + d253 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d581, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4779 p hg
    simpa only [d581, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d581, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4751 p hg
    simpa only [d581, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4794 (p : Pattern) (guard : d854 p = 1) : d582 p ≤ (2 : Int) + d254 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d582, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4792 p hg
    simpa only [d582, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d582, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4793 p hg
    simpa only [d582, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4795 (p : Pattern) (guard : d854 p = 1) : d583 p ≤ (2 : Int) + d255 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d583, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4794 p hg
    simpa only [d583, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d583, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4769 p hg
    simpa only [d583, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4796 (p : Pattern) (guard : d854 p = 1) : d584 p ≤ (2 : Int) + d256 p := by
  cases selected : p 133 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d584, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4795 p hg
    simpa only [d584, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d584, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4769 p hg
    simpa only [d584, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4797 (p : Pattern) (guard : d854 p = 1) : d585 p ≤ (2 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d585, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4791 p hg
    simpa only [d585, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d585, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4796 p hg
    simpa only [d585, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4798 (p : Pattern) (guard : d854 p = 1) : d586 p ≤ (2 : Int) + d258 p := by
  cases selected : p 108 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d586, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4771 p hg
    simpa only [d586, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d586, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4797 p hg
    simpa only [d586, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4799 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (0 : Int) + d28 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4800 (p : Pattern) (guard : d1175 p = 1) : d24 p ≤ (0 : Int) + d29 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1175, d24, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2785 p hg
    simpa only [d1175, d24, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d24, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4799 p hg
    simpa only [d1175, d24, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4801 (p : Pattern) (guard : d1175 p = 1) : d24 p ≤ (0 : Int) + d30 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1175, d24, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2790 p hg
    simpa only [d1175, d24, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d24, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4799 p hg
    simpa only [d1175, d24, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4802 (p : Pattern) (guard : d1175 p = 1) : d24 p ≤ (0 : Int) + d31 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4800 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4801 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4803 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (0 : Int) + d587 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4804 (p : Pattern) (guard : d1175 p = 1) : d525 p ≤ (0 : Int) + d588 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1175, d525, d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2794 p hg
    simpa only [d1175, d525, d588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d525, d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4803 p hg
    simpa only [d1175, d525, d588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4805 (p : Pattern) (guard : d1175 p = 1) : d526 p ≤ (0 : Int) + d589 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d526, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4800 p hg
    simpa only [d526, d589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d526, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4804 p hg
    simpa only [d526, d589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4806 (p : Pattern) (guard : d1175 p = 1) : d525 p ≤ (0 : Int) + d590 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1175, d525, d590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2800 p hg
    simpa only [d1175, d525, d590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d525, d590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4803 p hg
    simpa only [d1175, d525, d590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4807 (p : Pattern) (guard : d1175 p = 1) : d526 p ≤ (0 : Int) + d591 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d526, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4801 p hg
    simpa only [d526, d591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d526, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4806 p hg
    simpa only [d526, d591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4808 (p : Pattern) (guard : d1175 p = 1) : d526 p ≤ (0 : Int) + d592 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4805 p hg
    simpa only [d592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4807 p hg
    simpa only [d592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4809 (p : Pattern) (guard : d1175 p = 1) : d527 p ≤ (0 : Int) + d593 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d527, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4802 p hg
    simpa only [d527, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d527, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4808 p hg
    simpa only [d527, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4810 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (0 : Int) + d32 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4811 (p : Pattern) (guard : d1175 p = 1) : d25 p ≤ (0 : Int) + d32 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1175, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2806 p hg
    simpa only [d1175, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4810 p hg
    simpa only [d1175, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4812 (p : Pattern) (guard : d1175 p = 1) : d26 p ≤ (0 : Int) + d33 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d26, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4801 p hg
    simpa only [d26, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d26, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4811 p hg
    simpa only [d26, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4813 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (0 : Int) + d594 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4814 (p : Pattern) (guard : d1175 p = 1) : d528 p ≤ (0 : Int) + d594 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1175, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2812 p hg
    simpa only [d1175, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4813 p hg
    simpa only [d1175, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4815 (p : Pattern) (guard : d1175 p = 1) : d529 p ≤ (0 : Int) + d595 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d529, d595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4811 p hg
    simpa only [d529, d595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d529, d595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4814 p hg
    simpa only [d529, d595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4816 (p : Pattern) (guard : d1175 p = 1) : d530 p ≤ (0 : Int) + d596 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d530, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4807 p hg
    simpa only [d530, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d530, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4815 p hg
    simpa only [d530, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4817 (p : Pattern) (guard : d1175 p = 1) : d531 p ≤ (0 : Int) + d597 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d531, d597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4812 p hg
    simpa only [d531, d597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d531, d597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4816 p hg
    simpa only [d531, d597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4818 (p : Pattern) (guard : d1175 p = 1) : d532 p ≤ (0 : Int) + d598 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d532, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4809 p hg
    simpa only [d532, d598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d532, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4817 p hg
    simpa only [d532, d598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4819 (p : Pattern) (guard : d1175 p = 1) : d525 p ≤ (0 : Int) + d599 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4804 p hg
    simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4806 p hg
    simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4820 (p : Pattern) (guard : d1175 p = 1) : d533 p ≤ (0 : Int) + d600 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d533, d600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4802 p hg
    simpa only [d533, d600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d533, d600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4819 p hg
    simpa only [d533, d600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4821 (p : Pattern) (guard : d1175 p = 1) : d534 p ≤ (0 : Int) + d601 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d534, d601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4800 p hg
    simpa only [d534, d601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d534, d601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4804 p hg
    simpa only [d534, d601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4822 (p : Pattern) (guard : d1175 p = 1) : d535 p ≤ (0 : Int) + d602 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d535, d602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4800 p hg
    simpa only [d535, d602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d535, d602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4821 p hg
    simpa only [d535, d602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4823 (p : Pattern) (guard : d1175 p = 1) : d534 p ≤ (0 : Int) + d603 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d534, d603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4801 p hg
    simpa only [d534, d603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d534, d603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4806 p hg
    simpa only [d534, d603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4824 (p : Pattern) (guard : d1175 p = 1) : d535 p ≤ (0 : Int) + d604 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d535, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4801 p hg
    simpa only [d535, d604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d535, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4823 p hg
    simpa only [d535, d604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4825 (p : Pattern) (guard : d1175 p = 1) : d535 p ≤ (0 : Int) + d605 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4822 p hg
    simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4824 p hg
    simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4826 (p : Pattern) (guard : d1175 p = 1) : d536 p ≤ (0 : Int) + d606 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d536, d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4825 p hg
    simpa only [d536, d606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d536, d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4819 p hg
    simpa only [d536, d606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4827 (p : Pattern) (guard : d1175 p = 1) : d537 p ≤ (0 : Int) + d607 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d537, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4820 p hg
    simpa only [d537, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d537, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4826 p hg
    simpa only [d537, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4828 (p : Pattern) (guard : d1175 p = 1) : d538 p ≤ (0 : Int) + d608 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d538, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4820 p hg
    simpa only [d538, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d538, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4827 p hg
    simpa only [d538, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4829 (p : Pattern) (guard : d1175 p = 1) : d539 p ≤ (0 : Int) + d609 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d539, d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4806 p hg
    simpa only [d539, d609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d539, d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4814 p hg
    simpa only [d539, d609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4830 (p : Pattern) (guard : d1175 p = 1) : d540 p ≤ (0 : Int) + d610 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d540, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4812 p hg
    simpa only [d540, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d540, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4829 p hg
    simpa only [d540, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4831 (p : Pattern) (guard : d1175 p = 1) : d541 p ≤ (0 : Int) + d611 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d541, d611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4811 p hg
    simpa only [d541, d611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d541, d611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4814 p hg
    simpa only [d541, d611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4832 (p : Pattern) (guard : d1175 p = 1) : d542 p ≤ (0 : Int) + d612 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d542, d612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4811 p hg
    simpa only [d542, d612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d542, d612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4831 p hg
    simpa only [d542, d612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4833 (p : Pattern) (guard : d1175 p = 1) : d543 p ≤ (0 : Int) + d613 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d543, d613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4824 p hg
    simpa only [d543, d613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d543, d613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4832 p hg
    simpa only [d543, d613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4834 (p : Pattern) (guard : d1175 p = 1) : d544 p ≤ (0 : Int) + d614 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d544, d614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4833 p hg
    simpa only [d544, d614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d544, d614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4829 p hg
    simpa only [d544, d614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4835 (p : Pattern) (guard : d1175 p = 1) : d545 p ≤ (0 : Int) + d615 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d545, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4830 p hg
    simpa only [d545, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d545, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4834 p hg
    simpa only [d545, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4836 (p : Pattern) (guard : d1175 p = 1) : d546 p ≤ (0 : Int) + d616 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d546, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4830 p hg
    simpa only [d546, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d546, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4835 p hg
    simpa only [d546, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4837 (p : Pattern) (guard : d1175 p = 1) : d547 p ≤ (0 : Int) + d617 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d547, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4828 p hg
    simpa only [d547, d617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d547, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4836 p hg
    simpa only [d547, d617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4838 (p : Pattern) (guard : d1175 p = 1) : d548 p ≤ (0 : Int) + d618 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d548, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4818 p hg
    simpa only [d548, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d548, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4837 p hg
    simpa only [d548, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4839 (p : Pattern) (guard : d1175 p = 1) : d549 p ≤ (0 : Int) + d619 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d549, d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4809 p hg
    simpa only [d549, d619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d549, d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4819 p hg
    simpa only [d549, d619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4840 (p : Pattern) (guard : d1175 p = 1) : d550 p ≤ (0 : Int) + d620 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d550, d620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4817 p hg
    simpa only [d550, d620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d550, d620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4829 p hg
    simpa only [d550, d620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4841 (p : Pattern) (guard : d1175 p = 1) : d551 p ≤ (0 : Int) + d621 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d551, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4839 p hg
    simpa only [d551, d621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d551, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4840 p hg
    simpa only [d551, d621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4842 (p : Pattern) (guard : d1175 p = 1) : d552 p ≤ (0 : Int) + d622 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d552, d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4827 p hg
    simpa only [d552, d622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d552, d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4819 p hg
    simpa only [d552, d622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4843 (p : Pattern) (guard : d1175 p = 1) : d553 p ≤ (0 : Int) + d623 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d553, d623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4835 p hg
    simpa only [d553, d623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d553, d623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4829 p hg
    simpa only [d553, d623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4844 (p : Pattern) (guard : d1175 p = 1) : d554 p ≤ (0 : Int) + d624 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d554, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4842 p hg
    simpa only [d554, d624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d554, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4843 p hg
    simpa only [d554, d624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4845 (p : Pattern) (guard : d1175 p = 1) : d555 p ≤ (0 : Int) + d625 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d555, d625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4841 p hg
    simpa only [d555, d625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d555, d625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4844 p hg
    simpa only [d555, d625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4846 (p : Pattern) (guard : d1175 p = 1) : d556 p ≤ (0 : Int) + d626 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d556, d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4838 p hg
    simpa only [d556, d626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d556, d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4845 p hg
    simpa only [d556, d626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4847 (p : Pattern) (guard : d1175 p = 1) : d557 p ≤ (0 : Int) + d627 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d557, d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4819 p hg
    simpa only [d557, d627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d557, d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4829 p hg
    simpa only [d557, d627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4848 (p : Pattern) (guard : d1175 p = 1) : d558 p ≤ (0 : Int) + d628 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d558, d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4845 p hg
    simpa only [d558, d628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d558, d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4847 p hg
    simpa only [d558, d628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4849 (p : Pattern) (guard : d1175 p = 1) : d559 p ≤ (0 : Int) + d629 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d559, d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4846 p hg
    simpa only [d559, d629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d559, d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4848 p hg
    simpa only [d559, d629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4850 (p : Pattern) (guard : d1175 p = 1) : d560 p ≤ (0 : Int) + d630 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d560, d630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4821 p hg
    simpa only [d560, d630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d560, d630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4804 p hg
    simpa only [d560, d630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4851 (p : Pattern) (guard : d1175 p = 1) : d560 p ≤ (0 : Int) + d631 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d560, d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4823 p hg
    simpa only [d560, d631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d560, d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4806 p hg
    simpa only [d560, d631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4852 (p : Pattern) (guard : d1175 p = 1) : d560 p ≤ (0 : Int) + d632 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4850 p hg
    simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4851 p hg
    simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4853 (p : Pattern) (guard : d1175 p = 1) : d561 p ≤ (0 : Int) + d633 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d561, d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4825 p hg
    simpa only [d561, d633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d561, d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4852 p hg
    simpa only [d561, d633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4854 (p : Pattern) (guard : d1175 p = 1) : d562 p ≤ (0 : Int) + d634 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d562, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4809 p hg
    simpa only [d562, d634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d562, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4853 p hg
    simpa only [d562, d634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4855 (p : Pattern) (guard : d1175 p = 1) : d563 p ≤ (0 : Int) + d635 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d563, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4809 p hg
    simpa only [d563, d635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d563, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4854 p hg
    simpa only [d563, d635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4856 (p : Pattern) (guard : d1175 p = 1) : d564 p ≤ (0 : Int) + d636 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d564, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4831 p hg
    simpa only [d564, d636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d564, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4814 p hg
    simpa only [d564, d636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4857 (p : Pattern) (guard : d1175 p = 1) : d565 p ≤ (0 : Int) + d637 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d565, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4851 p hg
    simpa only [d565, d637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d565, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4856 p hg
    simpa only [d565, d637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4858 (p : Pattern) (guard : d1175 p = 1) : d566 p ≤ (0 : Int) + d638 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d566, d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4833 p hg
    simpa only [d566, d638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d566, d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4857 p hg
    simpa only [d566, d638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4859 (p : Pattern) (guard : d1175 p = 1) : d567 p ≤ (0 : Int) + d639 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d567, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4817 p hg
    simpa only [d567, d639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d567, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4858 p hg
    simpa only [d567, d639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4860 (p : Pattern) (guard : d1175 p = 1) : d568 p ≤ (0 : Int) + d640 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d568, d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4817 p hg
    simpa only [d568, d640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d568, d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4859 p hg
    simpa only [d568, d640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4861 (p : Pattern) (guard : d1175 p = 1) : d569 p ≤ (0 : Int) + d641 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d569, d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4855 p hg
    simpa only [d569, d641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d569, d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4860 p hg
    simpa only [d569, d641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4862 (p : Pattern) (guard : d1175 p = 1) : d570 p ≤ (0 : Int) + d642 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d570, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4861 p hg
    simpa only [d570, d642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d570, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4847 p hg
    simpa only [d570, d642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4863 (p : Pattern) (guard : d1175 p = 1) : d571 p ≤ (0 : Int) + d643 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d571, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4802 p hg
    simpa only [d571, d643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d571, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4852 p hg
    simpa only [d571, d643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4864 (p : Pattern) (guard : d1175 p = 1) : d572 p ≤ (0 : Int) + d644 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d572, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4863 p hg
    simpa only [d572, d644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d572, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4853 p hg
    simpa only [d572, d644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4865 (p : Pattern) (guard : d1175 p = 1) : d573 p ≤ (0 : Int) + d645 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d573, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4864 p hg
    simpa only [d573, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d573, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4819 p hg
    simpa only [d573, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4866 (p : Pattern) (guard : d1175 p = 1) : d574 p ≤ (0 : Int) + d646 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d574, d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4812 p hg
    simpa only [d574, d646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d574, d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4857 p hg
    simpa only [d574, d646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4867 (p : Pattern) (guard : d1175 p = 1) : d575 p ≤ (0 : Int) + d647 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d575, d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4866 p hg
    simpa only [d575, d647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d575, d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4858 p hg
    simpa only [d575, d647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4868 (p : Pattern) (guard : d1175 p = 1) : d576 p ≤ (0 : Int) + d648 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d576, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4867 p hg
    simpa only [d576, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d576, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4829 p hg
    simpa only [d576, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4869 (p : Pattern) (guard : d1175 p = 1) : d577 p ≤ (0 : Int) + d649 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d577, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4865 p hg
    simpa only [d577, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d577, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4868 p hg
    simpa only [d577, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4870 (p : Pattern) (guard : d1175 p = 1) : d578 p ≤ (0 : Int) + d650 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d578, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4869 p hg
    simpa only [d578, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d578, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4847 p hg
    simpa only [d578, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4871 (p : Pattern) (guard : d1175 p = 1) : d579 p ≤ (0 : Int) + d651 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d579, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4862 p hg
    simpa only [d579, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d579, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4870 p hg
    simpa only [d579, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4872 (p : Pattern) (guard : d1175 p = 1) : d580 p ≤ (0 : Int) + d652 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d580, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4854 p hg
    simpa only [d580, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d580, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4819 p hg
    simpa only [d580, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4873 (p : Pattern) (guard : d1175 p = 1) : d581 p ≤ (0 : Int) + d653 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d581, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4859 p hg
    simpa only [d581, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d581, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4829 p hg
    simpa only [d581, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4874 (p : Pattern) (guard : d1175 p = 1) : d582 p ≤ (0 : Int) + d654 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d582, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4872 p hg
    simpa only [d582, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d582, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4873 p hg
    simpa only [d582, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4875 (p : Pattern) (guard : d1175 p = 1) : d583 p ≤ (0 : Int) + d655 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d583, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4874 p hg
    simpa only [d583, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d583, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4847 p hg
    simpa only [d583, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4876 (p : Pattern) (guard : d1175 p = 1) : d584 p ≤ (0 : Int) + d656 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d584, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4875 p hg
    simpa only [d584, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d584, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4847 p hg
    simpa only [d584, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4877 (p : Pattern) (guard : d1175 p = 1) : d585 p ≤ (0 : Int) + d657 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d585, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4871 p hg
    simpa only [d585, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d585, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4876 p hg
    simpa only [d585, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4878 (p : Pattern) (guard : d1175 p = 1) : d586 p ≤ (0 : Int) + d658 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d586, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4849 p hg
    simpa only [d586, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d586, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4877 p hg
    simpa only [d586, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4879 (p : Pattern) (guard : d916 p = 1) : d0 p ≤ (3 : Int) + d0 p := by
  omega
theorem compare4880 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (3 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4881 (p : Pattern) (guard : d1176 p = 1) : d24 p ≤ (3 : Int) + d0 p := by
  cases selected : p 192 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d1176, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4879 p hg
    simpa only [d1176, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1176, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4880 p hg
    simpa only [d1176, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4882 (p : Pattern) (guard : d916 p = 1) : d2 p ≤ (3 : Int) + d2 p := by
  omega
theorem compare4883 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (3 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4884 (p : Pattern) (guard : d1176 p = 1) : d525 p ≤ (3 : Int) + d2 p := by
  cases selected : p 192 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d1176, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4882 p hg
    simpa only [d1176, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1176, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4883 p hg
    simpa only [d1176, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4885 (p : Pattern) (guard : d1176 p = 1) : d526 p ≤ (3 : Int) + d45 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d526, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4881 p hg
    simpa only [d526, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d526, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4884 p hg
    simpa only [d526, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4886 (p : Pattern) (guard : d1176 p = 1) : d527 p ≤ (3 : Int) + d46 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d527, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4881 p hg
    simpa only [d527, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d527, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4885 p hg
    simpa only [d527, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4887 (p : Pattern) (guard : d916 p = 1) : d8 p ≤ (3 : Int) + d8 p := by
  omega
theorem compare4888 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (3 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4889 (p : Pattern) (guard : d1176 p = 1) : d25 p ≤ (3 : Int) + d8 p := by
  cases selected : p 192 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d1176, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4887 p hg
    simpa only [d1176, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1176, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4888 p hg
    simpa only [d1176, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4890 (p : Pattern) (guard : d1176 p = 1) : d26 p ≤ (3 : Int) + d1055 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d26, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4881 p hg
    simpa only [d26, d1055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d26, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4889 p hg
    simpa only [d26, d1055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4891 (p : Pattern) (guard : d916 p = 1) : d9 p ≤ (3 : Int) + d9 p := by
  omega
theorem compare4892 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (3 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4893 (p : Pattern) (guard : d1176 p = 1) : d528 p ≤ (3 : Int) + d9 p := by
  cases selected : p 192 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d1176, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4891 p hg
    simpa only [d1176, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1176, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4892 p hg
    simpa only [d1176, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4894 (p : Pattern) (guard : d1176 p = 1) : d529 p ≤ (3 : Int) + d1056 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d529, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4889 p hg
    simpa only [d529, d1056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d529, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d529, d1056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4895 (p : Pattern) (guard : d1176 p = 1) : d530 p ≤ (3 : Int) + d1057 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d530, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4885 p hg
    simpa only [d530, d1057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d530, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4894 p hg
    simpa only [d530, d1057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4896 (p : Pattern) (guard : d1176 p = 1) : d531 p ≤ (3 : Int) + d1058 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d531, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4890 p hg
    simpa only [d531, d1058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d531, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4895 p hg
    simpa only [d531, d1058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4897 (p : Pattern) (guard : d1176 p = 1) : d532 p ≤ (3 : Int) + d1059 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d532, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4886 p hg
    simpa only [d532, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d532, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4896 p hg
    simpa only [d532, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4898 (p : Pattern) (guard : d1176 p = 1) : d533 p ≤ (3 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d533, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4881 p hg
    simpa only [d533, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d533, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4884 p hg
    simpa only [d533, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4899 (p : Pattern) (guard : d1176 p = 1) : d534 p ≤ (3 : Int) + d82 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1176 p = 1 := by simpa only [d534, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4881 p hg
    simpa only [d534, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d534, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4884 p hg
    simpa only [d534, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
