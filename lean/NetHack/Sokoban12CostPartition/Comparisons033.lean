/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons032
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare4620 (p : Pattern) (guard : d854 p = 1) : d550 p ≤ (0 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d550, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4601 p hg
    simpa only [d550, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d550, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4609 p hg
    simpa only [d550, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4621 (p : Pattern) (guard : d854 p = 1) : d551 p ≤ (0 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d551, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4619 p hg
    simpa only [d551, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d551, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4620 p hg
    simpa only [d551, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4622 (p : Pattern) (guard : d854 p = 1) : d552 p ≤ (0 : Int) + d181 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d552, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4607 p hg
    simpa only [d552, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d552, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4591 p hg
    simpa only [d552, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4623 (p : Pattern) (guard : d854 p = 1) : d553 p ≤ (0 : Int) + d240 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d553, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4615 p hg
    simpa only [d553, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d553, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4609 p hg
    simpa only [d553, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4624 (p : Pattern) (guard : d854 p = 1) : d554 p ≤ (0 : Int) + d241 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d554, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4622 p hg
    simpa only [d554, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d554, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4623 p hg
    simpa only [d554, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4625 (p : Pattern) (guard : d854 p = 1) : d555 p ≤ (0 : Int) + d242 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d555, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4621 p hg
    simpa only [d555, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d555, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4624 p hg
    simpa only [d555, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4626 (p : Pattern) (guard : d854 p = 1) : d556 p ≤ (0 : Int) + d243 p := by
  cases selected : p 133 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d556, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4618 p hg
    simpa only [d556, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d556, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4625 p hg
    simpa only [d556, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4627 (p : Pattern) (guard : d854 p = 1) : d557 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d557, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4591 p hg
    simpa only [d557, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d557, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4609 p hg
    simpa only [d557, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4628 (p : Pattern) (guard : d854 p = 1) : d558 p ≤ (0 : Int) + d244 p := by
  cases selected : p 133 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d558, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4625 p hg
    simpa only [d558, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d558, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4627 p hg
    simpa only [d558, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4629 (p : Pattern) (guard : d854 p = 1) : d559 p ≤ (0 : Int) + d245 p := by
  cases selected : p 132 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d559, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4626 p hg
    simpa only [d559, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d559, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4628 p hg
    simpa only [d559, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4630 (p : Pattern) (guard : d854 p = 1) : d560 p ≤ (0 : Int) + d137 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d560, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4604 p hg
    simpa only [d560, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d560, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4591 p hg
    simpa only [d560, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4631 (p : Pattern) (guard : d854 p = 1) : d561 p ≤ (0 : Int) + d139 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d561, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4605 p hg
    simpa only [d561, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d561, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4630 p hg
    simpa only [d561, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4632 (p : Pattern) (guard : d854 p = 1) : d562 p ≤ (0 : Int) + d153 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d562, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4593 p hg
    simpa only [d562, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d562, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4631 p hg
    simpa only [d562, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4633 (p : Pattern) (guard : d854 p = 1) : d563 p ≤ (0 : Int) + d186 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d563, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4593 p hg
    simpa only [d563, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d563, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4632 p hg
    simpa only [d563, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4634 (p : Pattern) (guard : d854 p = 1) : d564 p ≤ (0 : Int) + d143 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d564, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4611 p hg
    simpa only [d564, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d564, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4598 p hg
    simpa only [d564, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4635 (p : Pattern) (guard : d854 p = 1) : d565 p ≤ (0 : Int) + d144 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d565, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4630 p hg
    simpa only [d565, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d565, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4634 p hg
    simpa only [d565, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4636 (p : Pattern) (guard : d854 p = 1) : d566 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d566, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4613 p hg
    simpa only [d566, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d566, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4635 p hg
    simpa only [d566, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4637 (p : Pattern) (guard : d854 p = 1) : d567 p ≤ (0 : Int) + d155 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d567, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4601 p hg
    simpa only [d567, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d567, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4636 p hg
    simpa only [d567, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4638 (p : Pattern) (guard : d854 p = 1) : d568 p ≤ (0 : Int) + d246 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d568, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4601 p hg
    simpa only [d568, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d568, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4637 p hg
    simpa only [d568, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4639 (p : Pattern) (guard : d854 p = 1) : d569 p ≤ (0 : Int) + d247 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d569, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4633 p hg
    simpa only [d569, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d569, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4638 p hg
    simpa only [d569, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4640 (p : Pattern) (guard : d854 p = 1) : d570 p ≤ (0 : Int) + d248 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d570, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4639 p hg
    simpa only [d570, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d570, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4627 p hg
    simpa only [d570, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4641 (p : Pattern) (guard : d854 p = 1) : d571 p ≤ (0 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d571, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4589 p hg
    simpa only [d571, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d571, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4630 p hg
    simpa only [d571, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4642 (p : Pattern) (guard : d854 p = 1) : d572 p ≤ (0 : Int) + d140 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d572, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4641 p hg
    simpa only [d572, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d572, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4631 p hg
    simpa only [d572, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4643 (p : Pattern) (guard : d854 p = 1) : d573 p ≤ (0 : Int) + d188 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d573, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4642 p hg
    simpa only [d573, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d573, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4591 p hg
    simpa only [d573, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4644 (p : Pattern) (guard : d854 p = 1) : d574 p ≤ (0 : Int) + d145 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d574, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4596 p hg
    simpa only [d574, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d574, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4635 p hg
    simpa only [d574, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4645 (p : Pattern) (guard : d854 p = 1) : d575 p ≤ (0 : Int) + d147 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d575, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4644 p hg
    simpa only [d575, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d575, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4636 p hg
    simpa only [d575, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4646 (p : Pattern) (guard : d854 p = 1) : d576 p ≤ (0 : Int) + d249 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d576, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4645 p hg
    simpa only [d576, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d576, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4609 p hg
    simpa only [d576, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4647 (p : Pattern) (guard : d854 p = 1) : d577 p ≤ (0 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d577, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4643 p hg
    simpa only [d577, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d577, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4646 p hg
    simpa only [d577, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4648 (p : Pattern) (guard : d854 p = 1) : d578 p ≤ (0 : Int) + d251 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d578, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4647 p hg
    simpa only [d578, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d578, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4627 p hg
    simpa only [d578, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4649 (p : Pattern) (guard : d854 p = 1) : d579 p ≤ (0 : Int) + d252 p := by
  cases selected : p 133 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d579, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4640 p hg
    simpa only [d579, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d579, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4648 p hg
    simpa only [d579, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4650 (p : Pattern) (guard : d854 p = 1) : d580 p ≤ (0 : Int) + d191 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d580, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4632 p hg
    simpa only [d580, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d580, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4591 p hg
    simpa only [d580, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4651 (p : Pattern) (guard : d854 p = 1) : d581 p ≤ (0 : Int) + d253 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d581, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4637 p hg
    simpa only [d581, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d581, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4609 p hg
    simpa only [d581, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4652 (p : Pattern) (guard : d854 p = 1) : d582 p ≤ (0 : Int) + d254 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d582, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4650 p hg
    simpa only [d582, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d582, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4651 p hg
    simpa only [d582, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4653 (p : Pattern) (guard : d854 p = 1) : d583 p ≤ (0 : Int) + d255 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d583, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4652 p hg
    simpa only [d583, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d583, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4627 p hg
    simpa only [d583, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4654 (p : Pattern) (guard : d854 p = 1) : d584 p ≤ (0 : Int) + d256 p := by
  cases selected : p 133 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d584, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4653 p hg
    simpa only [d584, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d584, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4627 p hg
    simpa only [d584, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4655 (p : Pattern) (guard : d854 p = 1) : d585 p ≤ (0 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d585, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4649 p hg
    simpa only [d585, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d585, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4654 p hg
    simpa only [d585, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4656 (p : Pattern) (guard : d854 p = 1) : d586 p ≤ (0 : Int) + d258 p := by
  cases selected : p 108 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d586, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4629 p hg
    simpa only [d586, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d586, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4655 p hg
    simpa only [d586, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4657 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (3 : Int) + d0 p := by
  omega
theorem compare4658 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (3 : Int) + d6 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4659 (p : Pattern) (guard : d854 p = 1) : d24 p ≤ (3 : Int) + d7 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d854, d24, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4657 p hg
    simpa only [d854, d24, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d24, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4658 p hg
    simpa only [d854, d24, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4660 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (3 : Int) + d2 p := by
  omega
theorem compare4661 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (3 : Int) + d54 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4662 (p : Pattern) (guard : d854 p = 1) : d525 p ≤ (3 : Int) + d55 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d854, d525, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4660 p hg
    simpa only [d854, d525, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d525, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4661 p hg
    simpa only [d854, d525, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4663 (p : Pattern) (guard : d854 p = 1) : d526 p ≤ (3 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d526, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4659 p hg
    simpa only [d526, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d526, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4662 p hg
    simpa only [d526, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4664 (p : Pattern) (guard : d854 p = 1) : d527 p ≤ (3 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d527, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4659 p hg
    simpa only [d527, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d527, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4663 p hg
    simpa only [d527, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4665 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (3 : Int) + d8 p := by
  omega
theorem compare4666 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (3 : Int) + d10 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4667 (p : Pattern) (guard : d854 p = 1) : d25 p ≤ (3 : Int) + d11 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d854, d25, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4665 p hg
    simpa only [d854, d25, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d25, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4666 p hg
    simpa only [d854, d25, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4668 (p : Pattern) (guard : d854 p = 1) : d26 p ≤ (3 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d26, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4659 p hg
    simpa only [d26, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d26, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4667 p hg
    simpa only [d26, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4669 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (3 : Int) + d9 p := by
  omega
theorem compare4670 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (3 : Int) + d59 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4671 (p : Pattern) (guard : d854 p = 1) : d528 p ≤ (3 : Int) + d60 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d854, d528, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4669 p hg
    simpa only [d854, d528, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d528, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4670 p hg
    simpa only [d854, d528, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4672 (p : Pattern) (guard : d854 p = 1) : d529 p ≤ (3 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d529, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4667 p hg
    simpa only [d529, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d529, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4671 p hg
    simpa only [d529, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4673 (p : Pattern) (guard : d854 p = 1) : d530 p ≤ (3 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d530, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4663 p hg
    simpa only [d530, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d530, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4672 p hg
    simpa only [d530, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4674 (p : Pattern) (guard : d854 p = 1) : d531 p ≤ (3 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d531, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4668 p hg
    simpa only [d531, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d531, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4673 p hg
    simpa only [d531, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4675 (p : Pattern) (guard : d854 p = 1) : d532 p ≤ (3 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d532, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4664 p hg
    simpa only [d532, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d532, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4674 p hg
    simpa only [d532, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4676 (p : Pattern) (guard : d854 p = 1) : d533 p ≤ (3 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d533, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4659 p hg
    simpa only [d533, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d533, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4662 p hg
    simpa only [d533, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4677 (p : Pattern) (guard : d854 p = 1) : d534 p ≤ (3 : Int) + d119 p := by
  cases selected : p 187 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d534, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4659 p hg
    simpa only [d534, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d534, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4662 p hg
    simpa only [d534, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4678 (p : Pattern) (guard : d854 p = 1) : d535 p ≤ (3 : Int) + d120 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d535, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4659 p hg
    simpa only [d535, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d535, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4677 p hg
    simpa only [d535, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4679 (p : Pattern) (guard : d854 p = 1) : d536 p ≤ (3 : Int) + d121 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d536, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4678 p hg
    simpa only [d536, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d536, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4662 p hg
    simpa only [d536, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4680 (p : Pattern) (guard : d854 p = 1) : d537 p ≤ (3 : Int) + d122 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d537, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4676 p hg
    simpa only [d537, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d537, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4679 p hg
    simpa only [d537, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4681 (p : Pattern) (guard : d854 p = 1) : d538 p ≤ (3 : Int) + d179 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d538, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4676 p hg
    simpa only [d538, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d538, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4680 p hg
    simpa only [d538, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4682 (p : Pattern) (guard : d854 p = 1) : d539 p ≤ (3 : Int) + d65 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d539, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4662 p hg
    simpa only [d539, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d539, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4671 p hg
    simpa only [d539, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4683 (p : Pattern) (guard : d854 p = 1) : d540 p ≤ (3 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d540, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4668 p hg
    simpa only [d540, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d540, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4682 p hg
    simpa only [d540, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4684 (p : Pattern) (guard : d854 p = 1) : d541 p ≤ (3 : Int) + d125 p := by
  cases selected : p 187 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d541, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4667 p hg
    simpa only [d541, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d541, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4671 p hg
    simpa only [d541, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4685 (p : Pattern) (guard : d854 p = 1) : d542 p ≤ (3 : Int) + d126 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d542, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4667 p hg
    simpa only [d542, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d542, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4684 p hg
    simpa only [d542, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4686 (p : Pattern) (guard : d854 p = 1) : d543 p ≤ (3 : Int) + d127 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d543, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4678 p hg
    simpa only [d543, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d543, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4685 p hg
    simpa only [d543, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4687 (p : Pattern) (guard : d854 p = 1) : d544 p ≤ (3 : Int) + d128 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d544, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4686 p hg
    simpa only [d544, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d544, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4682 p hg
    simpa only [d544, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4688 (p : Pattern) (guard : d854 p = 1) : d545 p ≤ (3 : Int) + d129 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d545, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4683 p hg
    simpa only [d545, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d545, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4687 p hg
    simpa only [d545, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4689 (p : Pattern) (guard : d854 p = 1) : d546 p ≤ (3 : Int) + d237 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d546, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4683 p hg
    simpa only [d546, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d546, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d546, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4690 (p : Pattern) (guard : d854 p = 1) : d547 p ≤ (3 : Int) + d238 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d547, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4681 p hg
    simpa only [d547, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d547, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4689 p hg
    simpa only [d547, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4691 (p : Pattern) (guard : d854 p = 1) : d548 p ≤ (3 : Int) + d239 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d548, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4675 p hg
    simpa only [d548, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d548, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4690 p hg
    simpa only [d548, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4692 (p : Pattern) (guard : d854 p = 1) : d549 p ≤ (3 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d549, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4664 p hg
    simpa only [d549, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d549, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4662 p hg
    simpa only [d549, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4693 (p : Pattern) (guard : d854 p = 1) : d550 p ≤ (3 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d550, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4674 p hg
    simpa only [d550, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d550, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4682 p hg
    simpa only [d550, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4694 (p : Pattern) (guard : d854 p = 1) : d551 p ≤ (3 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d551, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4692 p hg
    simpa only [d551, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d551, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4693 p hg
    simpa only [d551, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4695 (p : Pattern) (guard : d854 p = 1) : d552 p ≤ (3 : Int) + d181 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d552, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4680 p hg
    simpa only [d552, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d552, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4662 p hg
    simpa only [d552, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4696 (p : Pattern) (guard : d854 p = 1) : d553 p ≤ (3 : Int) + d240 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d553, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d553, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d553, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4682 p hg
    simpa only [d553, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4697 (p : Pattern) (guard : d854 p = 1) : d554 p ≤ (3 : Int) + d241 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d554, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4695 p hg
    simpa only [d554, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d554, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4696 p hg
    simpa only [d554, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4698 (p : Pattern) (guard : d854 p = 1) : d555 p ≤ (3 : Int) + d242 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d555, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4694 p hg
    simpa only [d555, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d555, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4697 p hg
    simpa only [d555, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4699 (p : Pattern) (guard : d854 p = 1) : d556 p ≤ (3 : Int) + d243 p := by
  cases selected : p 133 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d556, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4691 p hg
    simpa only [d556, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d556, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4698 p hg
    simpa only [d556, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4700 (p : Pattern) (guard : d854 p = 1) : d557 p ≤ (3 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d557, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4662 p hg
    simpa only [d557, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d557, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4682 p hg
    simpa only [d557, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4701 (p : Pattern) (guard : d854 p = 1) : d558 p ≤ (3 : Int) + d244 p := by
  cases selected : p 133 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d558, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4698 p hg
    simpa only [d558, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d558, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4700 p hg
    simpa only [d558, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4702 (p : Pattern) (guard : d854 p = 1) : d559 p ≤ (3 : Int) + d245 p := by
  cases selected : p 132 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d559, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4699 p hg
    simpa only [d559, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d559, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4701 p hg
    simpa only [d559, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4703 (p : Pattern) (guard : d854 p = 1) : d560 p ≤ (3 : Int) + d137 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d560, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4677 p hg
    simpa only [d560, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d560, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4662 p hg
    simpa only [d560, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4704 (p : Pattern) (guard : d854 p = 1) : d561 p ≤ (3 : Int) + d139 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d561, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4678 p hg
    simpa only [d561, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d561, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4703 p hg
    simpa only [d561, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4705 (p : Pattern) (guard : d854 p = 1) : d562 p ≤ (3 : Int) + d153 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d562, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4664 p hg
    simpa only [d562, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d562, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4704 p hg
    simpa only [d562, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4706 (p : Pattern) (guard : d854 p = 1) : d563 p ≤ (3 : Int) + d186 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d563, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4664 p hg
    simpa only [d563, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d563, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4705 p hg
    simpa only [d563, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4707 (p : Pattern) (guard : d854 p = 1) : d564 p ≤ (3 : Int) + d143 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d564, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4684 p hg
    simpa only [d564, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d564, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4671 p hg
    simpa only [d564, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4708 (p : Pattern) (guard : d854 p = 1) : d565 p ≤ (3 : Int) + d144 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d565, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4703 p hg
    simpa only [d565, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d565, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4707 p hg
    simpa only [d565, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4709 (p : Pattern) (guard : d854 p = 1) : d566 p ≤ (3 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d566, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4686 p hg
    simpa only [d566, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d566, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4708 p hg
    simpa only [d566, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4710 (p : Pattern) (guard : d854 p = 1) : d567 p ≤ (3 : Int) + d155 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d567, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4674 p hg
    simpa only [d567, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d567, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4709 p hg
    simpa only [d567, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4711 (p : Pattern) (guard : d854 p = 1) : d568 p ≤ (3 : Int) + d246 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d568, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4674 p hg
    simpa only [d568, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d568, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4710 p hg
    simpa only [d568, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4712 (p : Pattern) (guard : d854 p = 1) : d569 p ≤ (3 : Int) + d247 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d569, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4706 p hg
    simpa only [d569, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d569, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4711 p hg
    simpa only [d569, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4713 (p : Pattern) (guard : d854 p = 1) : d570 p ≤ (3 : Int) + d248 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d570, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4712 p hg
    simpa only [d570, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d570, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4700 p hg
    simpa only [d570, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4714 (p : Pattern) (guard : d854 p = 1) : d571 p ≤ (3 : Int) + d138 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d571, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4659 p hg
    simpa only [d571, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d571, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4703 p hg
    simpa only [d571, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4715 (p : Pattern) (guard : d854 p = 1) : d572 p ≤ (3 : Int) + d140 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d572, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4714 p hg
    simpa only [d572, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d572, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4704 p hg
    simpa only [d572, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4716 (p : Pattern) (guard : d854 p = 1) : d573 p ≤ (3 : Int) + d188 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d573, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4715 p hg
    simpa only [d573, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d573, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4662 p hg
    simpa only [d573, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4717 (p : Pattern) (guard : d854 p = 1) : d574 p ≤ (3 : Int) + d145 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d574, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4668 p hg
    simpa only [d574, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d574, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4708 p hg
    simpa only [d574, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4718 (p : Pattern) (guard : d854 p = 1) : d575 p ≤ (3 : Int) + d147 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d575, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4717 p hg
    simpa only [d575, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d575, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4709 p hg
    simpa only [d575, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4719 (p : Pattern) (guard : d854 p = 1) : d576 p ≤ (3 : Int) + d249 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d576, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4718 p hg
    simpa only [d576, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d576, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4682 p hg
    simpa only [d576, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4720 (p : Pattern) (guard : d854 p = 1) : d577 p ≤ (3 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d577, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4716 p hg
    simpa only [d577, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d577, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4719 p hg
    simpa only [d577, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4721 (p : Pattern) (guard : d854 p = 1) : d578 p ≤ (3 : Int) + d251 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d578, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4720 p hg
    simpa only [d578, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d578, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4700 p hg
    simpa only [d578, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4722 (p : Pattern) (guard : d854 p = 1) : d579 p ≤ (3 : Int) + d252 p := by
  cases selected : p 133 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d579, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4713 p hg
    simpa only [d579, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d579, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4721 p hg
    simpa only [d579, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4723 (p : Pattern) (guard : d854 p = 1) : d580 p ≤ (3 : Int) + d191 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d580, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4705 p hg
    simpa only [d580, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d580, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4662 p hg
    simpa only [d580, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4724 (p : Pattern) (guard : d854 p = 1) : d581 p ≤ (3 : Int) + d253 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d581, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4710 p hg
    simpa only [d581, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d581, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4682 p hg
    simpa only [d581, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4725 (p : Pattern) (guard : d854 p = 1) : d582 p ≤ (3 : Int) + d254 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d582, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4723 p hg
    simpa only [d582, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d582, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4724 p hg
    simpa only [d582, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4726 (p : Pattern) (guard : d854 p = 1) : d583 p ≤ (3 : Int) + d255 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d583, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4725 p hg
    simpa only [d583, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d583, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4700 p hg
    simpa only [d583, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4727 (p : Pattern) (guard : d854 p = 1) : d584 p ≤ (3 : Int) + d256 p := by
  cases selected : p 133 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d584, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4726 p hg
    simpa only [d584, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d584, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4700 p hg
    simpa only [d584, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4728 (p : Pattern) (guard : d854 p = 1) : d585 p ≤ (3 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d585, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4722 p hg
    simpa only [d585, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d585, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4727 p hg
    simpa only [d585, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4729 (p : Pattern) (guard : d854 p = 1) : d586 p ≤ (3 : Int) + d258 p := by
  cases selected : p 108 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d586, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4702 p hg
    simpa only [d586, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d586, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4728 p hg
    simpa only [d586, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4730 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (2 : Int) + d6 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4731 (p : Pattern) (guard : d854 p = 1) : d24 p ≤ (2 : Int) + d7 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d854, d24, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2641 p hg
    simpa only [d854, d24, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d24, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4730 p hg
    simpa only [d854, d24, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4732 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (2 : Int) + d54 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4733 (p : Pattern) (guard : d854 p = 1) : d525 p ≤ (2 : Int) + d55 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d854, d525, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2645 p hg
    simpa only [d854, d525, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d525, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4732 p hg
    simpa only [d854, d525, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4734 (p : Pattern) (guard : d854 p = 1) : d526 p ≤ (2 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d526, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4731 p hg
    simpa only [d526, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d526, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4733 p hg
    simpa only [d526, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4735 (p : Pattern) (guard : d854 p = 1) : d527 p ≤ (2 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d527, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4731 p hg
    simpa only [d527, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d527, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4734 p hg
    simpa only [d527, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4736 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (2 : Int) + d10 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4737 (p : Pattern) (guard : d854 p = 1) : d25 p ≤ (2 : Int) + d11 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d854, d25, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2651 p hg
    simpa only [d854, d25, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d25, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4736 p hg
    simpa only [d854, d25, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4738 (p : Pattern) (guard : d854 p = 1) : d26 p ≤ (2 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d26, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4731 p hg
    simpa only [d26, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d26, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4737 p hg
    simpa only [d26, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4739 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (2 : Int) + d59 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4740 (p : Pattern) (guard : d854 p = 1) : d528 p ≤ (2 : Int) + d60 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d854, d528, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2656 p hg
    simpa only [d854, d528, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d528, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4739 p hg
    simpa only [d854, d528, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4741 (p : Pattern) (guard : d854 p = 1) : d529 p ≤ (2 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d529, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4737 p hg
    simpa only [d529, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d529, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4740 p hg
    simpa only [d529, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4742 (p : Pattern) (guard : d854 p = 1) : d530 p ≤ (2 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d530, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4734 p hg
    simpa only [d530, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d530, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4741 p hg
    simpa only [d530, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4743 (p : Pattern) (guard : d854 p = 1) : d531 p ≤ (2 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d531, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4738 p hg
    simpa only [d531, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d531, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4742 p hg
    simpa only [d531, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4744 (p : Pattern) (guard : d854 p = 1) : d532 p ≤ (2 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d532, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4735 p hg
    simpa only [d532, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d532, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4743 p hg
    simpa only [d532, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4745 (p : Pattern) (guard : d854 p = 1) : d533 p ≤ (2 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d533, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4731 p hg
    simpa only [d533, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d533, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4733 p hg
    simpa only [d533, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4746 (p : Pattern) (guard : d854 p = 1) : d534 p ≤ (2 : Int) + d119 p := by
  cases selected : p 187 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d534, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4731 p hg
    simpa only [d534, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d534, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4733 p hg
    simpa only [d534, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4747 (p : Pattern) (guard : d854 p = 1) : d535 p ≤ (2 : Int) + d120 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d535, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4731 p hg
    simpa only [d535, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d535, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4746 p hg
    simpa only [d535, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4748 (p : Pattern) (guard : d854 p = 1) : d536 p ≤ (2 : Int) + d121 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d536, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4747 p hg
    simpa only [d536, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d536, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4733 p hg
    simpa only [d536, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4749 (p : Pattern) (guard : d854 p = 1) : d537 p ≤ (2 : Int) + d122 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d537, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4745 p hg
    simpa only [d537, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d537, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4748 p hg
    simpa only [d537, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4750 (p : Pattern) (guard : d854 p = 1) : d538 p ≤ (2 : Int) + d179 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d538, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4745 p hg
    simpa only [d538, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d538, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4749 p hg
    simpa only [d538, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4751 (p : Pattern) (guard : d854 p = 1) : d539 p ≤ (2 : Int) + d65 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d539, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4733 p hg
    simpa only [d539, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d539, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4740 p hg
    simpa only [d539, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4752 (p : Pattern) (guard : d854 p = 1) : d540 p ≤ (2 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d540, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4738 p hg
    simpa only [d540, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d540, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4751 p hg
    simpa only [d540, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4753 (p : Pattern) (guard : d854 p = 1) : d541 p ≤ (2 : Int) + d125 p := by
  cases selected : p 187 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d541, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4737 p hg
    simpa only [d541, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d541, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4740 p hg
    simpa only [d541, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4754 (p : Pattern) (guard : d854 p = 1) : d542 p ≤ (2 : Int) + d126 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d542, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4737 p hg
    simpa only [d542, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d542, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4753 p hg
    simpa only [d542, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4755 (p : Pattern) (guard : d854 p = 1) : d543 p ≤ (2 : Int) + d127 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d543, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4747 p hg
    simpa only [d543, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d543, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4754 p hg
    simpa only [d543, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4756 (p : Pattern) (guard : d854 p = 1) : d544 p ≤ (2 : Int) + d128 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d544, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4755 p hg
    simpa only [d544, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d544, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4751 p hg
    simpa only [d544, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4757 (p : Pattern) (guard : d854 p = 1) : d545 p ≤ (2 : Int) + d129 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d545, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4752 p hg
    simpa only [d545, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d545, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4756 p hg
    simpa only [d545, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4758 (p : Pattern) (guard : d854 p = 1) : d546 p ≤ (2 : Int) + d237 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d546, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4752 p hg
    simpa only [d546, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d546, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4757 p hg
    simpa only [d546, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4759 (p : Pattern) (guard : d854 p = 1) : d547 p ≤ (2 : Int) + d238 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d547, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4750 p hg
    simpa only [d547, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d547, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4758 p hg
    simpa only [d547, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
