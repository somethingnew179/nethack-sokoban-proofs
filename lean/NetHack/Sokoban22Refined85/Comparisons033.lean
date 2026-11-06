/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons032
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare4620 (p : Pattern) (guard : d4117 p = 1) : d101 p ≤ (0 : Int) + d731 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d101, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4613 p hg
    simpa only [d101, d731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d101, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4619 p hg
    simpa only [d101, d731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4621 (p : Pattern) (guard : d4117 p = 1) : d88 p ≤ (0 : Int) + d735 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d88, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2815 p hg
    simpa only [d88, d735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d88, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4616 p hg
    simpa only [d88, d735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4622 (p : Pattern) (guard : d4117 p = 1) : d97 p ≤ (0 : Int) + d736 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d97, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4602 p hg
    simpa only [d97, d736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d97, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4611 p hg
    simpa only [d97, d736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4623 (p : Pattern) (guard : d4117 p = 1) : d98 p ≤ (0 : Int) + d737 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d98, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4621 p hg
    simpa only [d98, d737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d98, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4622 p hg
    simpa only [d98, d737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4624 (p : Pattern) (guard : d4117 p = 1) : d88 p ≤ (0 : Int) + d738 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d88, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2828 p hg
    simpa only [d88, d738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d88, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4616 p hg
    simpa only [d88, d738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4625 (p : Pattern) (guard : d4117 p = 1) : d100 p ≤ (0 : Int) + d739 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d100, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4624 p hg
    simpa only [d100, d739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d100, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4618 p hg
    simpa only [d100, d739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4626 (p : Pattern) (guard : d4117 p = 1) : d101 p ≤ (0 : Int) + d740 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d101, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4623 p hg
    simpa only [d101, d740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d101, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4625 p hg
    simpa only [d101, d740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4627 (p : Pattern) (guard : d4117 p = 1) : d101 p ≤ (0 : Int) + d741 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4620 p hg
    simpa only [d741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4626 p hg
    simpa only [d741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4628 (p : Pattern) (guard : d0 p = 1) : d151 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4629 (p : Pattern) (guard : d4117 p = 1) : d152 p ≤ (0 : Int) + d745 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d152, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d4117, d152, d745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d152, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4628 p hg
    simpa only [d4117, d152, d745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4630 (p : Pattern) (guard : d0 p = 1) : d155 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4631 (p : Pattern) (guard : d4117 p = 1) : d156 p ≤ (0 : Int) + d746 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d156, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1570 p hg
    simpa only [d4117, d156, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d156, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4630 p hg
    simpa only [d4117, d156, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4632 (p : Pattern) (guard : d4117 p = 1) : d157 p ≤ (0 : Int) + d747 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d157, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4629 p hg
    simpa only [d157, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d157, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4631 p hg
    simpa only [d157, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4633 (p : Pattern) (guard : d4117 p = 1) : d158 p ≤ (0 : Int) + d748 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d158, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2838 p hg
    simpa only [d158, d748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d158, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4632 p hg
    simpa only [d158, d748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4634 (p : Pattern) (guard : d0 p = 1) : d151 p ≤ (0 : Int) + d396 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4635 (p : Pattern) (guard : d4117 p = 1) : d152 p ≤ (0 : Int) + d749 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d152, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d4117, d152, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d152, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4634 p hg
    simpa only [d4117, d152, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4636 (p : Pattern) (guard : d4117 p = 1) : d157 p ≤ (0 : Int) + d750 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d157, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4635 p hg
    simpa only [d157, d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d157, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4631 p hg
    simpa only [d157, d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4637 (p : Pattern) (guard : d4117 p = 1) : d162 p ≤ (0 : Int) + d162 p := by
  omega
theorem compare4638 (p : Pattern) (guard : d4117 p = 1) : d163 p ≤ (0 : Int) + d751 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d163, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4636 p hg
    simpa only [d163, d751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d163, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4637 p hg
    simpa only [d163, d751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4639 (p : Pattern) (guard : d4117 p = 1) : d164 p ≤ (0 : Int) + d752 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d164, d752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4633 p hg
    simpa only [d164, d752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d164, d752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4638 p hg
    simpa only [d164, d752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4640 (p : Pattern) (guard : d4117 p = 1) : d158 p ≤ (0 : Int) + d755 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d158, d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2853 p hg
    simpa only [d158, d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d158, d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4632 p hg
    simpa only [d158, d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4641 (p : Pattern) (guard : d4117 p = 1) : d165 p ≤ (0 : Int) + d756 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d165, d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4632 p hg
    simpa only [d165, d756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d165, d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4444 p hg
    simpa only [d165, d756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4642 (p : Pattern) (guard : d4117 p = 1) : d166 p ≤ (0 : Int) + d757 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d166, d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4640 p hg
    simpa only [d166, d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d166, d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4641 p hg
    simpa only [d166, d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4643 (p : Pattern) (guard : d4117 p = 1) : d167 p ≤ (0 : Int) + d758 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d167, d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4639 p hg
    simpa only [d167, d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d167, d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4642 p hg
    simpa only [d167, d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4644 (p : Pattern) (guard : d4117 p = 1) : d168 p ≤ (0 : Int) + d759 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d168, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4620 p hg
    simpa only [d168, d759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d168, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4643 p hg
    simpa only [d168, d759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4645 (p : Pattern) (guard : d4117 p = 1) : d169 p ≤ (0 : Int) + d760 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d169, d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4627 p hg
    simpa only [d169, d760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d169, d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4644 p hg
    simpa only [d169, d760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4646 (p : Pattern) (guard : d0 p = 1) : d178 p ≤ (0 : Int) + d405 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4647 (p : Pattern) (guard : d4117 p = 1) : d179 p ≤ (0 : Int) + d717 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d179, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d179, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d179, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4646 p hg
    simpa only [d4117, d179, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4648 (p : Pattern) (guard : d0 p = 1) : d185 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4649 (p : Pattern) (guard : d4117 p = 1) : d186 p ≤ (0 : Int) + d714 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d186, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d4117, d186, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d186, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4648 p hg
    simpa only [d4117, d186, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4650 (p : Pattern) (guard : d4117 p = 1) : d187 p ≤ (0 : Int) + d718 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d187, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4647 p hg
    simpa only [d187, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d187, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4649 p hg
    simpa only [d187, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4651 (p : Pattern) (guard : d0 p = 1) : d196 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4652 (p : Pattern) (guard : d4117 p = 1) : d197 p ≤ (0 : Int) + d761 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d197, d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2866 p hg
    simpa only [d4117, d197, d761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d197, d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4651 p hg
    simpa only [d4117, d197, d761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4653 (p : Pattern) (guard : d0 p = 1) : d203 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4654 (p : Pattern) (guard : d4117 p = 1) : d204 p ≤ (0 : Int) + d762 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d204, d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2869 p hg
    simpa only [d4117, d204, d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d204, d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4653 p hg
    simpa only [d4117, d204, d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4655 (p : Pattern) (guard : d4117 p = 1) : d205 p ≤ (0 : Int) + d763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d205, d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4652 p hg
    simpa only [d205, d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d205, d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4654 p hg
    simpa only [d205, d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4656 (p : Pattern) (guard : d4117 p = 1) : d206 p ≤ (0 : Int) + d764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d206, d764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4650 p hg
    simpa only [d206, d764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d206, d764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4655 p hg
    simpa only [d206, d764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4657 (p : Pattern) (guard : d4117 p = 1) : d207 p ≤ (0 : Int) + d765 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d207, d765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4655 p hg
    simpa only [d207, d765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d207, d765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4444 p hg
    simpa only [d207, d765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4658 (p : Pattern) (guard : d4117 p = 1) : d208 p ≤ (0 : Int) + d766 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d208, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4656 p hg
    simpa only [d208, d766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d208, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4657 p hg
    simpa only [d208, d766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4659 (p : Pattern) (guard : d4117 p = 1) : d209 p ≤ (0 : Int) + d767 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d209, d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4623 p hg
    simpa only [d209, d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d209, d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4658 p hg
    simpa only [d209, d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4660 (p : Pattern) (guard : d4117 p = 1) : d210 p ≤ (0 : Int) + d768 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d210, d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4620 p hg
    simpa only [d210, d768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d210, d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4659 p hg
    simpa only [d210, d768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4661 (p : Pattern) (guard : d4117 p = 1) : d221 p ≤ (0 : Int) + d771 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d221, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1411 p hg
    simpa only [d4117, d221, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d221, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4630 p hg
    simpa only [d4117, d221, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4662 (p : Pattern) (guard : d4117 p = 1) : d222 p ≤ (0 : Int) + d772 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d222, d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4629 p hg
    simpa only [d222, d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d222, d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4661 p hg
    simpa only [d222, d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4663 (p : Pattern) (guard : d4117 p = 1) : d223 p ≤ (0 : Int) + d773 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d223, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2879 p hg
    simpa only [d223, d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d223, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4662 p hg
    simpa only [d223, d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4664 (p : Pattern) (guard : d4117 p = 1) : d222 p ≤ (0 : Int) + d774 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d222, d774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4635 p hg
    simpa only [d222, d774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d222, d774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4661 p hg
    simpa only [d222, d774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4665 (p : Pattern) (guard : d4117 p = 1) : d224 p ≤ (0 : Int) + d775 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d224, d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4664 p hg
    simpa only [d224, d775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d224, d775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4637 p hg
    simpa only [d224, d775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4666 (p : Pattern) (guard : d4117 p = 1) : d225 p ≤ (0 : Int) + d776 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d225, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4663 p hg
    simpa only [d225, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d225, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4665 p hg
    simpa only [d225, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4667 (p : Pattern) (guard : d0 p = 1) : d232 p ≤ (0 : Int) + d405 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4668 (p : Pattern) (guard : d4117 p = 1) : d233 p ≤ (0 : Int) + d753 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d233, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d4117, d233, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d233, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4667 p hg
    simpa only [d4117, d233, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4669 (p : Pattern) (guard : d0 p = 1) : d238 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4670 (p : Pattern) (guard : d4117 p = 1) : d239 p ≤ (0 : Int) + d771 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d239, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1411 p hg
    simpa only [d4117, d239, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d239, d771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4669 p hg
    simpa only [d4117, d239, d771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4671 (p : Pattern) (guard : d4117 p = 1) : d240 p ≤ (0 : Int) + d777 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d240, d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4668 p hg
    simpa only [d240, d777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d240, d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4670 p hg
    simpa only [d240, d777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4672 (p : Pattern) (guard : d1 p = 1) : d243 p ≤ (0 : Int) + d243 p := by
  omega
theorem compare4673 (p : Pattern) (guard : d4117 p = 1) : d244 p ≤ (0 : Int) + d778 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d244, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4672 p hg
    simpa only [d4117, d244, d778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d244, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4630 p hg
    simpa only [d4117, d244, d778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4674 (p : Pattern) (guard : d0 p = 1) : d248 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4675 (p : Pattern) (guard : d4117 p = 1) : d249 p ≤ (0 : Int) + d779 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d249, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2897 p hg
    simpa only [d4117, d249, d779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d249, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4674 p hg
    simpa only [d4117, d249, d779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4676 (p : Pattern) (guard : d4117 p = 1) : d250 p ≤ (0 : Int) + d780 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d250, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4673 p hg
    simpa only [d250, d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d250, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4675 p hg
    simpa only [d250, d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4677 (p : Pattern) (guard : d4117 p = 1) : d251 p ≤ (0 : Int) + d781 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d251, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4671 p hg
    simpa only [d251, d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d251, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4676 p hg
    simpa only [d251, d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4678 (p : Pattern) (guard : d0 p = 1) : d259 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4679 (p : Pattern) (guard : d4117 p = 1) : d260 p ≤ (0 : Int) + d782 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d260, d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2894 p hg
    simpa only [d4117, d260, d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d260, d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4678 p hg
    simpa only [d4117, d260, d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4680 (p : Pattern) (guard : d4117 p = 1) : d261 p ≤ (0 : Int) + d783 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d261, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4679 p hg
    simpa only [d261, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d261, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4675 p hg
    simpa only [d261, d783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4681 (p : Pattern) (guard : d4117 p = 1) : d262 p ≤ (0 : Int) + d784 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d262, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4680 p hg
    simpa only [d262, d784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d262, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4444 p hg
    simpa only [d262, d784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4682 (p : Pattern) (guard : d4117 p = 1) : d263 p ≤ (0 : Int) + d785 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d263, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4677 p hg
    simpa only [d263, d785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d263, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4681 p hg
    simpa only [d263, d785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4683 (p : Pattern) (guard : d4117 p = 1) : d264 p ≤ (0 : Int) + d786 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d264, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4666 p hg
    simpa only [d264, d786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d264, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4682 p hg
    simpa only [d264, d786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4684 (p : Pattern) (guard : d4117 p = 1) : d265 p ≤ (0 : Int) + d787 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d265, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4620 p hg
    simpa only [d265, d787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d265, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4683 p hg
    simpa only [d265, d787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4685 (p : Pattern) (guard : d4117 p = 1) : d266 p ≤ (0 : Int) + d788 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d266, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4660 p hg
    simpa only [d266, d788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d266, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4684 p hg
    simpa only [d266, d788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4686 (p : Pattern) (guard : d4117 p = 1) : d267 p ≤ (0 : Int) + d789 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d267, d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4645 p hg
    simpa only [d267, d789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d267, d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4685 p hg
    simpa only [d267, d789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4687 (p : Pattern) (guard : d0 p = 1) : d29 p ≤ (2 : Int) + d28 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4688 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d14 p := by
  omega
theorem compare4689 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (2 : Int) + d0 p := by
  change (2 : Int) ≤ (2 : Int) + 0
  decide
theorem compare4690 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (2 : Int) + d13 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4689 p hg
    simpa only [d30, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d30, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4691 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (2 : Int) + d14 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4689 p hg
    simpa only [d31, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4690 p hg
    simpa only [d31, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4692 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (2 : Int) + d15 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4691 p hg
    simpa only [d32, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d32, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4693 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (2 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d33, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d33, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d33, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4692 p hg
    simpa only [d33, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4694 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (2 : Int) + d4 p := by
  change (0 : Int) ≤ (2 : Int) + 4
  decide
theorem compare4695 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (2 : Int) + d17 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4694 p hg
    simpa only [d13, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d13, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4696 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d18 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4694 p hg
    simpa only [d14, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4695 p hg
    simpa only [d14, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4697 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (2 : Int) + d4 p := by
  change (6 : Int) ≤ (2 : Int) + 4
  decide
theorem compare4698 (p : Pattern) (guard : d1 p = 1) : d34 p ≤ (2 : Int) + d17 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4697 p hg
    simpa only [d34, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d34, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4699 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (2 : Int) + d18 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d35, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4697 p hg
    simpa only [d35, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d35, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4698 p hg
    simpa only [d35, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4700 (p : Pattern) (guard : d1 p = 1) : d36 p ≤ (2 : Int) + d19 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d36, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4699 p hg
    simpa only [d36, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d36, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d36, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4701 (p : Pattern) (guard : d1 p = 1) : d37 p ≤ (2 : Int) + d20 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d37, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4696 p hg
    simpa only [d37, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d37, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4700 p hg
    simpa only [d37, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4702 (p : Pattern) (guard : d1 p = 1) : d38 p ≤ (2 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d38, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4693 p hg
    simpa only [d38, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d38, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4701 p hg
    simpa only [d38, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4703 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (2 : Int) + d9 p := by
  change (0 : Int) ≤ (2 : Int) + 9
  decide
theorem compare4704 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (2 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4703 p hg
    simpa only [d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d13, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4705 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4703 p hg
    simpa only [d14, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4704 p hg
    simpa only [d14, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4706 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (2 : Int) + d9 p := by
  change (11 : Int) ≤ (2 : Int) + 9
  decide
theorem compare4707 (p : Pattern) (guard : d1 p = 1) : d39 p ≤ (2 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4706 p hg
    simpa only [d39, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d39, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4708 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (2 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d40, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4706 p hg
    simpa only [d40, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d40, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4707 p hg
    simpa only [d40, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4709 (p : Pattern) (guard : d1 p = 1) : d41 p ≤ (2 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d41, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4708 p hg
    simpa only [d41, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d41, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d41, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4710 (p : Pattern) (guard : d1 p = 1) : d42 p ≤ (2 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d42, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4705 p hg
    simpa only [d42, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d42, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4709 p hg
    simpa only [d42, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4711 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (2 : Int) + d12 p := by
  change (4 : Int) ≤ (2 : Int) + 12
  decide
theorem compare4712 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4711 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4713 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4711 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4712 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4714 (p : Pattern) (guard : d1 p = 1) : d43 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4713 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4715 (p : Pattern) (guard : d1 p = 1) : d44 p ≤ (2 : Int) + d27 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d44, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4710 p hg
    simpa only [d44, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d44, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4714 p hg
    simpa only [d44, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4716 (p : Pattern) (guard : d1 p = 1) : d45 p ≤ (2 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d45, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4702 p hg
    simpa only [d45, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d45, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4715 p hg
    simpa only [d45, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4717 (p : Pattern) (guard : d0 p = 1) : d50 p ≤ (2 : Int) + d28 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4718 (p : Pattern) (guard : d4299 p = 1) : d51 p ≤ (2 : Int) + d28 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4716 p hg
    simpa only [d4299, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4717 p hg
    simpa only [d4299, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4719 (p : Pattern) (guard : d4432 p = 1) : d52 p ≤ (2 : Int) + d28 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4687 p hg
    simpa only [d4432, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4718 p hg
    simpa only [d4432, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4720 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (2 : Int) + d64 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4721 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (2 : Int) + d10 p := by
  change (2 : Int) ≤ (2 : Int) + 10
  decide
theorem compare4722 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (2 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4721 p hg
    simpa only [d30, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d30, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4723 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (2 : Int) + d58 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4721 p hg
    simpa only [d31, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4722 p hg
    simpa only [d31, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4724 (p : Pattern) (guard : d1 p = 1) : d66 p ≤ (2 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d66, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4723 p hg
    simpa only [d66, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d66, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2207 p hg
    simpa only [d66, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4725 (p : Pattern) (guard : d1 p = 1) : d67 p ≤ (2 : Int) + d61 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d67, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4701 p hg
    simpa only [d67, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d67, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4724 p hg
    simpa only [d67, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4726 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (2 : Int) + d11 p := by
  change (4 : Int) ≤ (2 : Int) + 11
  decide
theorem compare4727 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (2 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4726 p hg
    simpa only [d17, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d17, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4728 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (2 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4726 p hg
    simpa only [d18, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4727 p hg
    simpa only [d18, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4729 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (2 : Int) + d11 p := by
  change (12 : Int) ≤ (2 : Int) + 11
  decide
theorem compare4730 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (2 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4729 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4731 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (2 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4729 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4730 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4732 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (2 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4731 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4733 (p : Pattern) (guard : d1 p = 1) : d43 p ≤ (2 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d43, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4728 p hg
    simpa only [d43, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d43, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4732 p hg
    simpa only [d43, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4734 (p : Pattern) (guard : d1 p = 1) : d68 p ≤ (2 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4733 p hg
    simpa only [d68, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1837 p hg
    simpa only [d68, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4735 (p : Pattern) (guard : d1 p = 1) : d69 p ≤ (2 : Int) + d64 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d69, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4725 p hg
    simpa only [d69, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d69, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4734 p hg
    simpa only [d69, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4736 (p : Pattern) (guard : d0 p = 1) : d74 p ≤ (2 : Int) + d64 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4737 (p : Pattern) (guard : d4299 p = 1) : d75 p ≤ (2 : Int) + d64 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4735 p hg
    simpa only [d4299, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4736 p hg
    simpa only [d4299, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4738 (p : Pattern) (guard : d4432 p = 1) : d76 p ≤ (2 : Int) + d64 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4720 p hg
    simpa only [d4432, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4737 p hg
    simpa only [d4432, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4739 (p : Pattern) (guard : d4432 p = 1) : d77 p ≤ (2 : Int) + d4433 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d77, d4433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4719 p hg
    simpa only [d77, d4433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d77, d4433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4738 p hg
    simpa only [d77, d4433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4740 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (2 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d53, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4691 p hg
    simpa only [d53, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d53, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4692 p hg
    simpa only [d53, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4741 (p : Pattern) (guard : d1 p = 1) : d78 p ≤ (2 : Int) + d20 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d78, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4699 p hg
    simpa only [d78, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d78, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4700 p hg
    simpa only [d78, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4742 (p : Pattern) (guard : d1 p = 1) : d79 p ≤ (2 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d79, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4740 p hg
    simpa only [d79, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d79, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4741 p hg
    simpa only [d79, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4743 (p : Pattern) (guard : d1 p = 1) : d62 p ≤ (2 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d62, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4708 p hg
    simpa only [d62, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d62, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4709 p hg
    simpa only [d62, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4744 (p : Pattern) (guard : d1 p = 1) : d63 p ≤ (2 : Int) + d27 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d63, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4743 p hg
    simpa only [d63, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d63, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d63, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4745 (p : Pattern) (guard : d1 p = 1) : d80 p ≤ (2 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d80, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4742 p hg
    simpa only [d80, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d80, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4744 p hg
    simpa only [d80, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4746 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d28 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4747 (p : Pattern) (guard : d4299 p = 1) : d81 p ≤ (2 : Int) + d28 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4745 p hg
    simpa only [d4299, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4746 p hg
    simpa only [d4299, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4748 (p : Pattern) (guard : d4432 p = 1) : d82 p ≤ (2 : Int) + d28 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4687 p hg
    simpa only [d4432, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4747 p hg
    simpa only [d4432, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4749 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (2 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2178 p hg
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2207 p hg
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4750 (p : Pattern) (guard : d1 p = 1) : d83 p ≤ (2 : Int) + d61 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d83, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4741 p hg
    simpa only [d83, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d83, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4749 p hg
    simpa only [d83, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4751 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (2 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4731 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4732 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4752 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (2 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4751 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4753 (p : Pattern) (guard : d1 p = 1) : d84 p ≤ (2 : Int) + d64 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d84, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4750 p hg
    simpa only [d84, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d84, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4752 p hg
    simpa only [d84, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4754 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d64 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4755 (p : Pattern) (guard : d4299 p = 1) : d85 p ≤ (2 : Int) + d64 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4753 p hg
    simpa only [d4299, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4754 p hg
    simpa only [d4299, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4756 (p : Pattern) (guard : d4432 p = 1) : d86 p ≤ (2 : Int) + d64 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4432, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4720 p hg
    simpa only [d4432, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4299 p = 1 := by simpa only [d4432, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4755 p hg
    simpa only [d4432, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4757 (p : Pattern) (guard : d4432 p = 1) : d87 p ≤ (2 : Int) + d4433 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d87, d4433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4748 p hg
    simpa only [d87, d4433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d87, d4433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4756 p hg
    simpa only [d87, d4433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4758 (p : Pattern) (guard : d4432 p = 1) : d88 p ≤ (2 : Int) + d4433 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4432 p = 1 := by simpa only [d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4739 p hg
    simpa only [d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4432 p = 1 := by simpa only [d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4757 p hg
    simpa only [d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4759 (p : Pattern) (guard : d0 p = 1) : d92 p ≤ (2 : Int) + d91 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
