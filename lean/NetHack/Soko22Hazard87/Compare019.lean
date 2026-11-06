import NetHack.Soko22Hazard87.Compare018
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare4750 (p : Pattern) (guard : d140 p = 1) : d47683 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d139 p = 1 := by simpa only [d140, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4749 p hg
    simpa only [d140, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d140, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d140, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4751 (p : Pattern) (guard : d228 p = 1) : d47799 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d227 p = 1 := by simpa only [d228, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4735 p hg
    simpa only [d228, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d140 p = 1 := by simpa only [d228, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4750 p hg
    simpa only [d228, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4752 (p : Pattern) (guard : d229 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d228 p = 1 := by simpa only [d229, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4751 p hg
    simpa only [d229, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d229, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d229, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4753 (p : Pattern) (guard : d230 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d229 p = 1 := by simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4752 p hg
    simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d69 p = 1 := by simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4557 p hg
    simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4754 (p : Pattern) (guard : d231 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d230 p = 1 := by simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4753 p hg
    simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d70 p = 1 := by simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4559 p hg
    simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4755 (p : Pattern) (guard : d232 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d231 p = 1 := by simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4754 p hg
    simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d71 p = 1 := by simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4560 p hg
    simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4756 (p : Pattern) (guard : d233 p = 1) : d47804 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d233, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4518 p hg
    simpa only [d233, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d232 p = 1 := by simpa only [d233, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4755 p hg
    simpa only [d233, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4757 (p : Pattern) (guard : d234 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d234, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d234, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d233 p = 1 := by simpa only [d234, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4756 p hg
    simpa only [d234, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4758 (p : Pattern) (guard : d235 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d234 p = 1 := by simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4757 p hg
    simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d74 p = 1 := by simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4563 p hg
    simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4759 (p : Pattern) (guard : d236 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d235 p = 1 := by simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4758 p hg
    simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d75 p = 1 := by simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4565 p hg
    simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4760 (p : Pattern) (guard : d237 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d236 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4759 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4761 (p : Pattern) (guard : d238 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d237 p = 1 := by simpa only [d238, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4760 p hg
    simpa only [d238, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d238, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d238, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4762 (p : Pattern) (guard : d239 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d239, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d239, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d238 p = 1 := by simpa only [d239, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4761 p hg
    simpa only [d239, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4763 (p : Pattern) (guard : d240 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d239 p = 1 := by simpa only [d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4762 p hg
    simpa only [d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d79 p = 1 := by simpa only [d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4570 p hg
    simpa only [d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4764 (p : Pattern) (guard : d241 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d240 p = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4763 p hg
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4765 (p : Pattern) (guard : d242 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d241 p = 1 := by simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4764 p hg
    simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4766 (p : Pattern) (guard : d243 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d242 p = 1 := by simpa only [d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4765 p hg
    simpa only [d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4767 (p : Pattern) (guard : d244 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d243 p = 1 := by simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4766 p hg
    simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d83 p = 1 := by simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4574 p hg
    simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4768 (p : Pattern) (guard : d4355 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d244 p = 1 := by simpa only [d4355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4767 p hg
    simpa only [d4355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d4355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4769 (p : Pattern) (guard : d4356 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4355 p = 1 := by simpa only [d4356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4768 p hg
    simpa only [d4356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d85 p = 1 := by simpa only [d4356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4576 p hg
    simpa only [d4356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4770 (p : Pattern) (guard : d4357 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d4357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4356 p = 1 := by simpa only [d4357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4769 p hg
    simpa only [d4357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4771 (p : Pattern) (guard : d4358 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d4358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4357 p = 1 := by simpa only [d4358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4770 p hg
    simpa only [d4358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4772 (p : Pattern) (guard : d4359 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4359, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d4359, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4358 p = 1 := by simpa only [d4359, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4771 p hg
    simpa only [d4359, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4773 (p : Pattern) (guard : d4360 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d4360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4359 p = 1 := by simpa only [d4360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4772 p hg
    simpa only [d4360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4774 (p : Pattern) (guard : d4361 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d4360 p = 1 := by simpa only [d4361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4773 p hg
    simpa only [d4361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d4361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4775 (p : Pattern) (guard : d4362 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d4361 p = 1 := by simpa only [d4362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4774 p hg
    simpa only [d4362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d4362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4776 (p : Pattern) (guard : d4363 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d4362 p = 1 := by simpa only [d4363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4775 p hg
    simpa only [d4363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d4363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4777 (p : Pattern) (guard : d4364 p = 1) : d47865 p ≤ (-1 : Int) + d98795 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4363 p = 1 := by simpa only [d4364, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4776 p hg
    simpa only [d4364, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4364, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4585 p hg
    simpa only [d4364, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4778 (p : Pattern) (guard : d51652 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 48 with
  | false =>
    have hg : d51651 p = 1 := by simpa only [d51652, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4719 p hg
    simpa only [d51652, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4364 p = 1 := by simpa only [d51652, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4777 p hg
    simpa only [d51652, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4779 (p : Pattern) (guard : d51653 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d51653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d51653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51652 p = 1 := by simpa only [d51653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4778 p hg
    simpa only [d51653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4780 (p : Pattern) (guard : d51654 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d51654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d51654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51653 p = 1 := by simpa only [d51654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4779 p hg
    simpa only [d51654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4781 (p : Pattern) (guard : d51655 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d51655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d51655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51654 p = 1 := by simpa only [d51655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4780 p hg
    simpa only [d51655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4782 (p : Pattern) (guard : d51656 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d51656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d51656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51655 p = 1 := by simpa only [d51656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4781 p hg
    simpa only [d51656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4783 (p : Pattern) (guard : d51657 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d99 p = 1 := by simpa only [d51657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4591 p hg
    simpa only [d51657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51656 p = 1 := by simpa only [d51657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4782 p hg
    simpa only [d51657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4784 (p : Pattern) (guard : d280 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d157 p = 1 := by simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4650 p hg
    simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4785 (p : Pattern) (guard : d281 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d280 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4784 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4786 (p : Pattern) (guard : d282 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d281 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4785 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4787 (p : Pattern) (guard : d283 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d282 p = 1 := by simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4786 p hg
    simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4788 (p : Pattern) (guard : d284 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d283 p = 1 := by simpa only [d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4787 p hg
    simpa only [d284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4789 (p : Pattern) (guard : d285 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d284 p = 1 := by simpa only [d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4788 p hg
    simpa only [d285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4790 (p : Pattern) (guard : d286 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d285 p = 1 := by simpa only [d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4789 p hg
    simpa only [d286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4791 (p : Pattern) (guard : d287 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d204 p = 1 := by simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4666 p hg
    simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4792 (p : Pattern) (guard : d288 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d287 p = 1 := by simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4791 p hg
    simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4793 (p : Pattern) (guard : d289 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d288 p = 1 := by simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4792 p hg
    simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4794 (p : Pattern) (guard : d290 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d289 p = 1 := by simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4793 p hg
    simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4795 (p : Pattern) (guard : d291 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d283 p = 1 := by simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4787 p hg
    simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d290 p = 1 := by simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4794 p hg
    simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4796 (p : Pattern) (guard : d292 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d284 p = 1 := by simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4788 p hg
    simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d291 p = 1 := by simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4795 p hg
    simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4797 (p : Pattern) (guard : d293 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d292 p = 1 := by simpa only [d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4796 p hg
    simpa only [d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4798 (p : Pattern) (guard : d294 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d286 p = 1 := by simpa only [d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4790 p hg
    simpa only [d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293 p = 1 := by simpa only [d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4797 p hg
    simpa only [d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4799 (p : Pattern) (guard : d295 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d154 p = 1 := by simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4647 p hg
    simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4800 (p : Pattern) (guard : d296 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295 p = 1 := by simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4799 p hg
    simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4801 (p : Pattern) (guard : d297 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d296 p = 1 := by simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4800 p hg
    simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d116 p = 1 := by simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4608 p hg
    simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4802 (p : Pattern) (guard : d298 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d297 p = 1 := by simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4801 p hg
    simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4803 (p : Pattern) (guard : d299 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d298 p = 1 := by simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4802 p hg
    simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4804 (p : Pattern) (guard : d300 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d299 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4803 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4805 (p : Pattern) (guard : d301 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d153 p = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4646 p hg
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4806 (p : Pattern) (guard : d302 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d301 p = 1 := by simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4805 p hg
    simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4807 (p : Pattern) (guard : d303 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d302 p = 1 := by simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4806 p hg
    simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4808 (p : Pattern) (guard : d304 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d303 p = 1 := by simpa only [d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4807 p hg
    simpa only [d304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d123 p = 1 := by simpa only [d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4615 p hg
    simpa only [d304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4809 (p : Pattern) (guard : d305 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d304 p = 1 := by simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4808 p hg
    simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4810 (p : Pattern) (guard : d306 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d305 p = 1 := by simpa only [d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4809 p hg
    simpa only [d306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4811 (p : Pattern) (guard : d307 p = 1) : d4 p ≤ (-1 : Int) + d12 p := by
  have ha := bounds4 p
  have hb := bounds12 p
  omega
theorem compare4812 (p : Pattern) (guard : d127 p = 1) : d4 p ≤ (-1 : Int) + d12 p := by
  have ha := bounds4 p
  have hb := bounds12 p
  omega
theorem compare4813 (p : Pattern) (guard : d308 p = 1) : d47616 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d127 p = 1 := by simpa only [d308, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4812 p hg
    simpa only [d308, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d308, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d308, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4814 (p : Pattern) (guard : d309 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d309, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4811 p hg
    simpa only [d309, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d309, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4813 p hg
    simpa only [d309, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4815 (p : Pattern) (guard : d310 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4814 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4622 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4816 (p : Pattern) (guard : d311 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4815 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d130 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4623 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4817 (p : Pattern) (guard : d312 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d311 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4816 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4624 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4818 (p : Pattern) (guard : d313 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4817 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4819 (p : Pattern) (guard : d314 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d313 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4818 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4820 (p : Pattern) (guard : d315 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d314 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4819 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4627 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4821 (p : Pattern) (guard : d316 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d315 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4820 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4628 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4822 (p : Pattern) (guard : d317 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316 p = 1 := by simpa only [d317, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4821 p hg
    simpa only [d317, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d317, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4823 (p : Pattern) (guard : d318 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4822 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d137 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4630 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4824 (p : Pattern) (guard : d319 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d318 p = 1 := by simpa only [d319, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4823 p hg
    simpa only [d319, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d319, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d319, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4825 (p : Pattern) (guard : d320 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d319 p = 1 := by simpa only [d320, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4824 p hg
    simpa only [d320, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d320, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d320, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4826 (p : Pattern) (guard : d321 p = 1) : d47664 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d321, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d320 p = 1 := by simpa only [d321, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4825 p hg
    simpa only [d321, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4827 (p : Pattern) (guard : d322 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d321 p = 1 := by simpa only [d322, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4826 p hg
    simpa only [d322, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d322, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d322, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4828 (p : Pattern) (guard : d323 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4827 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d142 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4635 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4829 (p : Pattern) (guard : d324 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d323 p = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4828 p hg
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d143 p = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4636 p hg
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4830 (p : Pattern) (guard : d325 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324 p = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4829 p hg
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d144 p = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4637 p hg
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4831 (p : Pattern) (guard : d326 p = 1) : d47686 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d326, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4403 p hg
    simpa only [d326, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325 p = 1 := by simpa only [d326, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4830 p hg
    simpa only [d326, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4832 (p : Pattern) (guard : d327 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d327, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d327, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326 p = 1 := by simpa only [d327, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4831 p hg
    simpa only [d327, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4833 (p : Pattern) (guard : d328 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d327 p = 1 := by simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4832 p hg
    simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d147 p = 1 := by simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4640 p hg
    simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4834 (p : Pattern) (guard : d329 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d328 p = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4833 p hg
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d148 p = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4641 p hg
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4835 (p : Pattern) (guard : d330 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d329 p = 1 := by simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4834 p hg
    simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4836 (p : Pattern) (guard : d331 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d330 p = 1 := by simpa only [d331, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4835 p hg
    simpa only [d331, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d331, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d331, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4837 (p : Pattern) (guard : d332 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d332, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d332, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d331 p = 1 := by simpa only [d332, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4836 p hg
    simpa only [d332, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4838 (p : Pattern) (guard : d475 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4640 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4839 (p : Pattern) (guard : d6738 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d475 p = 1 := by simpa only [d6738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4838 p hg
    simpa only [d6738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34 p = 1 := by simpa only [d6738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4433 p hg
    simpa only [d6738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4840 (p : Pattern) (guard : d6739 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d6738 p = 1 := by simpa only [d6739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4839 p hg
    simpa only [d6739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d6739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4841 (p : Pattern) (guard : d6740 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6739 p = 1 := by simpa only [d6740, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4840 p hg
    simpa only [d6740, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6740, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d6740, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4842 (p : Pattern) (guard : d6741 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6741, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d6741, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6740 p = 1 := by simpa only [d6741, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4841 p hg
    simpa only [d6741, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4843 (p : Pattern) (guard : d6742 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d332 p = 1 := by simpa only [d6742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4837 p hg
    simpa only [d6742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6741 p = 1 := by simpa only [d6742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4842 p hg
    simpa only [d6742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4844 (p : Pattern) (guard : d6743 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6742 p = 1 := by simpa only [d6743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4843 p hg
    simpa only [d6743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4845 (p : Pattern) (guard : d6744 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6743 p = 1 := by simpa only [d6744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4844 p hg
    simpa only [d6744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4846 (p : Pattern) (guard : d6745 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6744 p = 1 := by simpa only [d6745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4845 p hg
    simpa only [d6745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4847 (p : Pattern) (guard : d6746 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6745 p = 1 := by simpa only [d6746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4846 p hg
    simpa only [d6746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d156 p = 1 := by simpa only [d6746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4649 p hg
    simpa only [d6746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4848 (p : Pattern) (guard : d82028 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6746 p = 1 := by simpa only [d82028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4847 p hg
    simpa only [d82028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4849 (p : Pattern) (guard : d4733 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d152 p = 1 := by simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4645 p hg
    simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4850 (p : Pattern) (guard : d4734 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d4733 p = 1 := by simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4849 p hg
    simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4851 (p : Pattern) (guard : d4735 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d4734 p = 1 := by simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4850 p hg
    simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4852 (p : Pattern) (guard : d4736 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d4736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4735 p = 1 := by simpa only [d4736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4851 p hg
    simpa only [d4736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4853 (p : Pattern) (guard : d4737 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d4736 p = 1 := by simpa only [d4737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4852 p hg
    simpa only [d4737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d4737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4854 (p : Pattern) (guard : d5350 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d4737 p = 1 := by simpa only [d5350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4853 p hg
    simpa only [d5350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d5350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4855 (p : Pattern) (guard : d82029 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d82028 p = 1 := by simpa only [d82029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4848 p hg
    simpa only [d82029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5350 p = 1 := by simpa only [d82029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4854 p hg
    simpa only [d82029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4856 (p : Pattern) (guard : d82030 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d306 p = 1 := by simpa only [d82030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4810 p hg
    simpa only [d82030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82029 p = 1 := by simpa only [d82030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4855 p hg
    simpa only [d82030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4857 (p : Pattern) (guard : d82031 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d300 p = 1 := by simpa only [d82031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4804 p hg
    simpa only [d82031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82030 p = 1 := by simpa only [d82031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4856 p hg
    simpa only [d82031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4858 (p : Pattern) (guard : d82032 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82031 p = 1 := by simpa only [d82032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4857 p hg
    simpa only [d82032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4859 (p : Pattern) (guard : d376 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295 p = 1 := by simpa only [d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4799 p hg
    simpa only [d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4860 (p : Pattern) (guard : d377 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d376 p = 1 := by simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4859 p hg
    simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d194 p = 1 := by simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4656 p hg
    simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4861 (p : Pattern) (guard : d378 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d377 p = 1 := by simpa only [d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4860 p hg
    simpa only [d378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4862 (p : Pattern) (guard : d379 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d378 p = 1 := by simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4861 p hg
    simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4863 (p : Pattern) (guard : d380 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d379 p = 1 := by simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4862 p hg
    simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4864 (p : Pattern) (guard : d381 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d302 p = 1 := by simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4806 p hg
    simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4865 (p : Pattern) (guard : d382 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d381 p = 1 := by simpa only [d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4864 p hg
    simpa only [d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d199 p = 1 := by simpa only [d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4661 p hg
    simpa only [d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4866 (p : Pattern) (guard : d383 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d382 p = 1 := by simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4865 p hg
    simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4867 (p : Pattern) (guard : d384 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d383 p = 1 := by simpa only [d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4866 p hg
    simpa only [d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4868 (p : Pattern) (guard : d6752 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6744 p = 1 := by simpa only [d6752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4845 p hg
    simpa only [d6752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4869 (p : Pattern) (guard : d6753 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6752 p = 1 := by simpa only [d6753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4868 p hg
    simpa only [d6753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d203 p = 1 := by simpa only [d6753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4665 p hg
    simpa only [d6753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4870 (p : Pattern) (guard : d82033 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6753 p = 1 := by simpa only [d82033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4869 p hg
    simpa only [d82033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4871 (p : Pattern) (guard : d5355 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d4735 p = 1 := by simpa only [d5355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4851 p hg
    simpa only [d5355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d5355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4872 (p : Pattern) (guard : d5356 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d5355 p = 1 := by simpa only [d5356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4871 p hg
    simpa only [d5356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d5356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4873 (p : Pattern) (guard : d5357 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d5356 p = 1 := by simpa only [d5357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4872 p hg
    simpa only [d5357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d5357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4874 (p : Pattern) (guard : d82034 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d82033 p = 1 := by simpa only [d82034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4870 p hg
    simpa only [d82034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5357 p = 1 := by simpa only [d82034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4873 p hg
    simpa only [d82034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4875 (p : Pattern) (guard : d82035 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d384 p = 1 := by simpa only [d82035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4867 p hg
    simpa only [d82035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82034 p = 1 := by simpa only [d82035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4874 p hg
    simpa only [d82035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4876 (p : Pattern) (guard : d82036 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d380 p = 1 := by simpa only [d82036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4863 p hg
    simpa only [d82036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82035 p = 1 := by simpa only [d82036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4875 p hg
    simpa only [d82036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4877 (p : Pattern) (guard : d82037 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d82031 p = 1 := by simpa only [d82037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4857 p hg
    simpa only [d82037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82036 p = 1 := by simpa only [d82037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4876 p hg
    simpa only [d82037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4878 (p : Pattern) (guard : d82038 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d82032 p = 1 := by simpa only [d82038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4858 p hg
    simpa only [d82038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82037 p = 1 := by simpa only [d82038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4877 p hg
    simpa only [d82038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4879 (p : Pattern) (guard : d397 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d283 p = 1 := by simpa only [d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4787 p hg
    simpa only [d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d103 p = 1 := by simpa only [d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4595 p hg
    simpa only [d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4880 (p : Pattern) (guard : d398 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d397 p = 1 := by simpa only [d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4879 p hg
    simpa only [d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d111 p = 1 := by simpa only [d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4603 p hg
    simpa only [d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4881 (p : Pattern) (guard : d82039 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d82038 p = 1 := by simpa only [d82039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4878 p hg
    simpa only [d82039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d398 p = 1 := by simpa only [d82039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4880 p hg
    simpa only [d82039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4882 (p : Pattern) (guard : d82040 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d82039 p = 1 := by simpa only [d82040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4881 p hg
    simpa only [d82040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4883 (p : Pattern) (guard : d82041 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d294 p = 1 := by simpa only [d82041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4798 p hg
    simpa only [d82041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82040 p = 1 := by simpa only [d82041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4882 p hg
    simpa only [d82041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4884 (p : Pattern) (guard : d307 p = 1) : d5 p ≤ (-1 : Int) + d12 p := by
  have ha := bounds5 p
  have hb := bounds12 p
  omega
theorem compare4885 (p : Pattern) (guard : d127 p = 1) : d5 p ≤ (-1 : Int) + d12 p := by
  have ha := bounds5 p
  have hb := bounds12 p
  omega
theorem compare4886 (p : Pattern) (guard : d308 p = 1) : d47705 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d127 p = 1 := by simpa only [d308, d47705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4885 p hg
    simpa only [d308, d47705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d308, d47705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d308, d47705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4887 (p : Pattern) (guard : d309 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d309, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4884 p hg
    simpa only [d309, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d309, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4886 p hg
    simpa only [d309, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4888 (p : Pattern) (guard : d310 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4887 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4681 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4889 (p : Pattern) (guard : d311 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4888 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d130 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4682 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4890 (p : Pattern) (guard : d312 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d311 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4889 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4683 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4891 (p : Pattern) (guard : d313 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4890 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4892 (p : Pattern) (guard : d314 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d313 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4891 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4893 (p : Pattern) (guard : d315 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d314 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4892 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4686 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4894 (p : Pattern) (guard : d316 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d315 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4687 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4895 (p : Pattern) (guard : d317 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316 p = 1 := by simpa only [d317, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4894 p hg
    simpa only [d317, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d317, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4896 (p : Pattern) (guard : d318 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4895 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d137 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4689 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4897 (p : Pattern) (guard : d319 p = 1) : d47735 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d318 p = 1 := by simpa only [d319, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4896 p hg
    simpa only [d319, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d319, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d319, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4898 (p : Pattern) (guard : d320 p = 1) : d47736 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d319 p = 1 := by simpa only [d320, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4897 p hg
    simpa only [d320, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d320, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d320, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4899 (p : Pattern) (guard : d321 p = 1) : d47737 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4465 p hg
    simpa only [d321, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d320 p = 1 := by simpa only [d321, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4898 p hg
    simpa only [d321, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4900 (p : Pattern) (guard : d322 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d321 p = 1 := by simpa only [d322, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4899 p hg
    simpa only [d322, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d322, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d322, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4901 (p : Pattern) (guard : d323 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4900 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d142 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4694 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4902 (p : Pattern) (guard : d324 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d323 p = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4901 p hg
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d143 p = 1 := by simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4695 p hg
    simpa only [d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4903 (p : Pattern) (guard : d325 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324 p = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4902 p hg
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d144 p = 1 := by simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4696 p hg
    simpa only [d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4904 (p : Pattern) (guard : d326 p = 1) : d47756 p ≤ (-1 : Int) + d47761 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d326, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4464 p hg
    simpa only [d326, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325 p = 1 := by simpa only [d326, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4903 p hg
    simpa only [d326, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4905 (p : Pattern) (guard : d327 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d327, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4463 p hg
    simpa only [d327, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326 p = 1 := by simpa only [d327, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4904 p hg
    simpa only [d327, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4906 (p : Pattern) (guard : d328 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d327 p = 1 := by simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4905 p hg
    simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d147 p = 1 := by simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4699 p hg
    simpa only [d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4907 (p : Pattern) (guard : d329 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d328 p = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4906 p hg
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d148 p = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4700 p hg
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4908 (p : Pattern) (guard : d330 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d329 p = 1 := by simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4907 p hg
    simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4909 (p : Pattern) (guard : d331 p = 1) : d47765 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d330 p = 1 := by simpa only [d331, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4908 p hg
    simpa only [d331, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d331, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d331, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4910 (p : Pattern) (guard : d332 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d332, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d332, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d331 p = 1 := by simpa only [d332, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4909 p hg
    simpa only [d332, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4911 (p : Pattern) (guard : d475 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4699 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4912 (p : Pattern) (guard : d6738 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d475 p = 1 := by simpa only [d6738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4911 p hg
    simpa only [d6738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34 p = 1 := by simpa only [d6738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4494 p hg
    simpa only [d6738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4913 (p : Pattern) (guard : d6739 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d6738 p = 1 := by simpa only [d6739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4912 p hg
    simpa only [d6739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d6739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4914 (p : Pattern) (guard : d6740 p = 1) : d47765 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6739 p = 1 := by simpa only [d6740, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4913 p hg
    simpa only [d6740, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6740, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d6740, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4915 (p : Pattern) (guard : d6741 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6741, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d6741, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6740 p = 1 := by simpa only [d6741, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4914 p hg
    simpa only [d6741, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4916 (p : Pattern) (guard : d6742 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d332 p = 1 := by simpa only [d6742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4910 p hg
    simpa only [d6742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6741 p = 1 := by simpa only [d6742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4915 p hg
    simpa only [d6742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4917 (p : Pattern) (guard : d6743 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6742 p = 1 := by simpa only [d6743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4916 p hg
    simpa only [d6743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4918 (p : Pattern) (guard : d6744 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6743 p = 1 := by simpa only [d6744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4917 p hg
    simpa only [d6744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4919 (p : Pattern) (guard : d6752 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6744 p = 1 := by simpa only [d6752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4918 p hg
    simpa only [d6752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4920 (p : Pattern) (guard : d6753 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6752 p = 1 := by simpa only [d6753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4919 p hg
    simpa only [d6753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d203 p = 1 := by simpa only [d6753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4708 p hg
    simpa only [d6753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4921 (p : Pattern) (guard : d82033 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6753 p = 1 := by simpa only [d82033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4920 p hg
    simpa only [d82033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d82033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4922 (p : Pattern) (guard : d4733 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d152 p = 1 := by simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4704 p hg
    simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4923 (p : Pattern) (guard : d4734 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d4733 p = 1 := by simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4922 p hg
    simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4924 (p : Pattern) (guard : d4735 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d4734 p = 1 := by simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4923 p hg
    simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4925 (p : Pattern) (guard : d5355 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d4735 p = 1 := by simpa only [d5355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4924 p hg
    simpa only [d5355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d5355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4926 (p : Pattern) (guard : d5356 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 91 with
  | false =>
    have hg : d5355 p = 1 := by simpa only [d5356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4925 p hg
    simpa only [d5356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d5356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4927 (p : Pattern) (guard : d5357 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 90 with
  | false =>
    have hg : d5356 p = 1 := by simpa only [d5357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4926 p hg
    simpa only [d5357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d5357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4928 (p : Pattern) (guard : d82034 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 89 with
  | false =>
    have hg : d82033 p = 1 := by simpa only [d82034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4921 p hg
    simpa only [d82034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5357 p = 1 := by simpa only [d82034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4927 p hg
    simpa only [d82034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4929 (p : Pattern) (guard : d82042 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d82042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82034 p = 1 := by simpa only [d82042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4928 p hg
    simpa only [d82042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4930 (p : Pattern) (guard : d82043 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d82043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82042 p = 1 := by simpa only [d82043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4929 p hg
    simpa only [d82043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4931 (p : Pattern) (guard : d82044 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82044, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82044, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82043 p = 1 := by simpa only [d82044, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4930 p hg
    simpa only [d82044, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4932 (p : Pattern) (guard : d82045 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d82045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82044 p = 1 := by simpa only [d82045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4931 p hg
    simpa only [d82045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4933 (p : Pattern) (guard : d107 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d50 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4504 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4934 (p : Pattern) (guard : d108 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 89 with
  | false =>
    have hg : d107 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4933 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4935 (p : Pattern) (guard : d109 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d108 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4934 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4936 (p : Pattern) (guard : d110 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d109 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4935 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4937 (p : Pattern) (guard : d406 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d406, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d406, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d110 p = 1 := by simpa only [d406, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4936 p hg
    simpa only [d406, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4938 (p : Pattern) (guard : d407 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d406 p = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4937 p hg
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4939 (p : Pattern) (guard : d82046 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 69 with
  | false =>
    have hg : d82045 p = 1 := by simpa only [d82046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4932 p hg
    simpa only [d82046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d407 p = 1 := by simpa only [d82046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4938 p hg
    simpa only [d82046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4940 (p : Pattern) (guard : d82047 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 51 with
  | false =>
    have hg : d82046 p = 1 := by simpa only [d82047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4939 p hg
    simpa only [d82047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d82047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4941 (p : Pattern) (guard : d82048 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 50 with
  | false =>
    have hg : d82047 p = 1 := by simpa only [d82048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4940 p hg
    simpa only [d82048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d82048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4942 (p : Pattern) (guard : d82049 p = 1) : d47768 p ≤ (-1 : Int) + d98793 p := by
  cases selected : p 49 with
  | false =>
    have hg : d82041 p = 1 := by simpa only [d82049, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4883 p hg
    simpa only [d82049, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82048 p = 1 := by simpa only [d82049, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4941 p hg
    simpa only [d82049, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4943 (p : Pattern) (guard : d307 p = 1) : d2 p ≤ (-1 : Int) + d12 p := by
  have ha := bounds2 p
  have hb := bounds12 p
  omega
theorem compare4944 (p : Pattern) (guard : d127 p = 1) : d2 p ≤ (-1 : Int) + d12 p := by
  have ha := bounds2 p
  have hb := bounds12 p
  omega
theorem compare4945 (p : Pattern) (guard : d308 p = 1) : d47629 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d127 p = 1 := by simpa only [d308, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4944 p hg
    simpa only [d308, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d308, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d308, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4946 (p : Pattern) (guard : d309 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d309, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4943 p hg
    simpa only [d309, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d309, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4945 p hg
    simpa only [d309, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4947 (p : Pattern) (guard : d310 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4946 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4723 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4948 (p : Pattern) (guard : d311 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4947 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d130 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4724 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4949 (p : Pattern) (guard : d312 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d311 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4948 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4725 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4950 (p : Pattern) (guard : d313 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4949 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4951 (p : Pattern) (guard : d314 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d313 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4950 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4952 (p : Pattern) (guard : d315 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d314 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4951 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4728 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4953 (p : Pattern) (guard : d316 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d315 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4952 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4729 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4954 (p : Pattern) (guard : d317 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316 p = 1 := by simpa only [d317, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4953 p hg
    simpa only [d317, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d317, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4955 (p : Pattern) (guard : d318 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4954 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d137 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4731 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4956 (p : Pattern) (guard : d412 p = 1) : d47652 p ≤ (-1 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d412, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d412, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318 p = 1 := by simpa only [d412, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4955 p hg
    simpa only [d412, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4957 (p : Pattern) (guard : d319 p = 1) : d47797 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d318 p = 1 := by simpa only [d319, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4823 p hg
    simpa only [d319, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d319, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d319, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4958 (p : Pattern) (guard : d413 p = 1) : d47798 p ≤ (-1 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d412 p = 1 := by simpa only [d413, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4956 p hg
    simpa only [d413, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d319 p = 1 := by simpa only [d413, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4957 p hg
    simpa only [d413, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4959 (p : Pattern) (guard : d307 p = 1) : d6 p ≤ (-1 : Int) + d12 p := by
  have ha := bounds6 p
  have hb := bounds12 p
  omega
theorem compare4960 (p : Pattern) (guard : d127 p = 1) : d6 p ≤ (-1 : Int) + d12 p := by
  have ha := bounds6 p
  have hb := bounds12 p
  omega
theorem compare4961 (p : Pattern) (guard : d308 p = 1) : d47633 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d127 p = 1 := by simpa only [d308, d47633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4960 p hg
    simpa only [d308, d47633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d308, d47633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d308, d47633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4962 (p : Pattern) (guard : d309 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d309, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4959 p hg
    simpa only [d309, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d309, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4961 p hg
    simpa only [d309, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4963 (p : Pattern) (guard : d310 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4962 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4739 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4964 (p : Pattern) (guard : d311 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4963 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d130 p = 1 := by simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4740 p hg
    simpa only [d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4965 (p : Pattern) (guard : d312 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d311 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4964 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4741 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4966 (p : Pattern) (guard : d313 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4965 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4967 (p : Pattern) (guard : d314 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d313 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4966 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4968 (p : Pattern) (guard : d315 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d314 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4967 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4744 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4969 (p : Pattern) (guard : d316 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d315 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4968 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4745 p hg
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4970 (p : Pattern) (guard : d317 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316 p = 1 := by simpa only [d317, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4969 p hg
    simpa only [d317, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d317, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4971 (p : Pattern) (guard : d318 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4970 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d137 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4747 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4972 (p : Pattern) (guard : d319 p = 1) : d47682 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d318 p = 1 := by simpa only [d319, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4971 p hg
    simpa only [d319, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d319, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d319, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4973 (p : Pattern) (guard : d320 p = 1) : d47683 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d319 p = 1 := by simpa only [d320, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4972 p hg
    simpa only [d320, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d320, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d320, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4974 (p : Pattern) (guard : d414 p = 1) : d47799 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d413 p = 1 := by simpa only [d414, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4958 p hg
    simpa only [d414, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d320 p = 1 := by simpa only [d414, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4973 p hg
    simpa only [d414, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4975 (p : Pattern) (guard : d415 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d414 p = 1 := by simpa only [d415, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4974 p hg
    simpa only [d415, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d415, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d415, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4976 (p : Pattern) (guard : d416 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d415 p = 1 := by simpa only [d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4975 p hg
    simpa only [d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d229 p = 1 := by simpa only [d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4752 p hg
    simpa only [d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4977 (p : Pattern) (guard : d417 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d416 p = 1 := by simpa only [d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4976 p hg
    simpa only [d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d230 p = 1 := by simpa only [d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4753 p hg
    simpa only [d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4978 (p : Pattern) (guard : d418 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d417 p = 1 := by simpa only [d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4977 p hg
    simpa only [d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d231 p = 1 := by simpa only [d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4754 p hg
    simpa only [d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4979 (p : Pattern) (guard : d419 p = 1) : d47804 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d419, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4518 p hg
    simpa only [d419, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d418 p = 1 := by simpa only [d419, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4978 p hg
    simpa only [d419, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4980 (p : Pattern) (guard : d420 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d420, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d420, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d419 p = 1 := by simpa only [d420, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4979 p hg
    simpa only [d420, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4981 (p : Pattern) (guard : d421 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d420 p = 1 := by simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4980 p hg
    simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d234 p = 1 := by simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4757 p hg
    simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4982 (p : Pattern) (guard : d422 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d421 p = 1 := by simpa only [d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4981 p hg
    simpa only [d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d235 p = 1 := by simpa only [d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4758 p hg
    simpa only [d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4983 (p : Pattern) (guard : d423 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d422 p = 1 := by simpa only [d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4982 p hg
    simpa only [d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4984 (p : Pattern) (guard : d424 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d423 p = 1 := by simpa only [d424, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4983 p hg
    simpa only [d424, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d424, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d424, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4985 (p : Pattern) (guard : d425 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d425, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d425, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d424 p = 1 := by simpa only [d425, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4984 p hg
    simpa only [d425, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4986 (p : Pattern) (guard : d673 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d234 p = 1 := by simpa only [d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4757 p hg
    simpa only [d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4987 (p : Pattern) (guard : d6771 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d673 p = 1 := by simpa only [d6771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4986 p hg
    simpa only [d6771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d75 p = 1 := by simpa only [d6771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4565 p hg
    simpa only [d6771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4988 (p : Pattern) (guard : d6772 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d6771 p = 1 := by simpa only [d6772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4987 p hg
    simpa only [d6772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d6772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4989 (p : Pattern) (guard : d6773 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6772 p = 1 := by simpa only [d6773, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4988 p hg
    simpa only [d6773, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6773, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d6773, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4990 (p : Pattern) (guard : d6774 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6774, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d6774, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6773 p = 1 := by simpa only [d6774, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4989 p hg
    simpa only [d6774, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4991 (p : Pattern) (guard : d6775 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d425 p = 1 := by simpa only [d6775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4985 p hg
    simpa only [d6775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6774 p = 1 := by simpa only [d6775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4990 p hg
    simpa only [d6775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4992 (p : Pattern) (guard : d6776 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6775 p = 1 := by simpa only [d6776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4991 p hg
    simpa only [d6776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4993 (p : Pattern) (guard : d6777 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6776 p = 1 := by simpa only [d6777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4992 p hg
    simpa only [d6777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4994 (p : Pattern) (guard : d6778 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6777 p = 1 := by simpa only [d6778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4993 p hg
    simpa only [d6778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4995 (p : Pattern) (guard : d6779 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6778 p = 1 := by simpa only [d6779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4994 p hg
    simpa only [d6779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d243 p = 1 := by simpa only [d6779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4766 p hg
    simpa only [d6779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4996 (p : Pattern) (guard : d82050 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6779 p = 1 := by simpa only [d82050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4995 p hg
    simpa only [d82050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d82050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4997 (p : Pattern) (guard : d5374 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d239 p = 1 := by simpa only [d5374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4762 p hg
    simpa only [d5374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d5374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4998 (p : Pattern) (guard : d5375 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d5374 p = 1 := by simpa only [d5375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4997 p hg
    simpa only [d5375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d5375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4999 (p : Pattern) (guard : d5376 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d5375 p = 1 := by simpa only [d5376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4998 p hg
    simpa only [d5376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d5376, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
