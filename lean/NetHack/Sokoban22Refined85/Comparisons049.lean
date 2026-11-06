/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons048
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare6860 (p : Pattern) (guard : d0 p = 1) : d78 p ≤ (2 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6861 (p : Pattern) (guard : d4148 p = 1) : d79 p ≤ (2 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4740 p hg
    simpa only [d4148, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6860 p hg
    simpa only [d4148, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6862 (p : Pattern) (guard : d4672 p = 1) : d188 p ≤ (2 : Int) + d16 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6672 p hg
    simpa only [d4672, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6861 p hg
    simpa only [d4672, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6863 (p : Pattern) (guard : d4673 p = 1) : d898 p ≤ (2 : Int) + d4681 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d898, d4681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6862 p hg
    simpa only [d4673, d898, d4681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d898, d4681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6753 p hg
    simpa only [d4673, d898, d4681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6864 (p : Pattern) (guard : d0 p = 1) : d193 p ≤ (2 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6865 (p : Pattern) (guard : d4148 p = 1) : d194 p ≤ (2 : Int) + d53 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4869 p hg
    simpa only [d4148, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6864 p hg
    simpa only [d4148, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6866 (p : Pattern) (guard : d4672 p = 1) : d899 p ≤ (2 : Int) + d53 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6705 p hg
    simpa only [d4672, d899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6865 p hg
    simpa only [d4672, d899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6867 (p : Pattern) (guard : d4673 p = 1) : d900 p ≤ (2 : Int) + d4682 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d900, d4682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6866 p hg
    simpa only [d4673, d900, d4682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d900, d4682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4673, d900, d4682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6868 (p : Pattern) (guard : d4673 p = 1) : d901 p ≤ (2 : Int) + d4683 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d901, d4683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6863 p hg
    simpa only [d901, d4683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d901, d4683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6867 p hg
    simpa only [d901, d4683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6869 (p : Pattern) (guard : d0 p = 1) : d62 p ≤ (2 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6870 (p : Pattern) (guard : d4148 p = 1) : d198 p ≤ (2 : Int) + d53 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4869 p hg
    simpa only [d4148, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6869 p hg
    simpa only [d4148, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6871 (p : Pattern) (guard : d4672 p = 1) : d199 p ≤ (2 : Int) + d53 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6705 p hg
    simpa only [d4672, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6870 p hg
    simpa only [d4672, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6872 (p : Pattern) (guard : d4673 p = 1) : d902 p ≤ (2 : Int) + d4684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d902, d4684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6871 p hg
    simpa only [d4673, d902, d4684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d902, d4684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6712 p hg
    simpa only [d4673, d902, d4684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6873 (p : Pattern) (guard : d0 p = 1) : d20 p ≤ (2 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6874 (p : Pattern) (guard : d4148 p = 1) : d83 p ≤ (2 : Int) + d20 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4741 p hg
    simpa only [d4148, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6712 p hg
    simpa only [d4148, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6875 (p : Pattern) (guard : d4672 p = 1) : d903 p ≤ (2 : Int) + d20 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6873 p hg
    simpa only [d4672, d903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6874 p hg
    simpa only [d4672, d903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6876 (p : Pattern) (guard : d4673 p = 1) : d904 p ≤ (2 : Int) + d4685 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d904, d4685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6875 p hg
    simpa only [d4673, d904, d4685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d904, d4685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4673, d904, d4685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6877 (p : Pattern) (guard : d4673 p = 1) : d905 p ≤ (2 : Int) + d4686 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d905, d4686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6872 p hg
    simpa only [d905, d4686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d905, d4686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6876 p hg
    simpa only [d905, d4686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6878 (p : Pattern) (guard : d4673 p = 1) : d906 p ≤ (2 : Int) + d4687 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d906, d4687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6868 p hg
    simpa only [d906, d4687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d906, d4687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6877 p hg
    simpa only [d906, d4687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6879 (p : Pattern) (guard : d4673 p = 1) : d907 p ≤ (2 : Int) + d4688 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d907, d4688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6781 p hg
    simpa only [d907, d4688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d907, d4688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6878 p hg
    simpa only [d907, d4688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6880 (p : Pattern) (guard : d4673 p = 1) : d908 p ≤ (2 : Int) + d4694 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d908, d4694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6878 p hg
    simpa only [d908, d4694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d908, d4694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6739 p hg
    simpa only [d908, d4694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6881 (p : Pattern) (guard : d4673 p = 1) : d909 p ≤ (2 : Int) + d4695 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d909, d4695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6879 p hg
    simpa only [d909, d4695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d909, d4695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6880 p hg
    simpa only [d909, d4695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6882 (p : Pattern) (guard : d4673 p = 1) : d910 p ≤ (2 : Int) + d4696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d910, d4696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6774 p hg
    simpa only [d910, d4696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d910, d4696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6881 p hg
    simpa only [d910, d4696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6883 (p : Pattern) (guard : d4673 p = 1) : d911 p ≤ (2 : Int) + d4696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6760 p hg
    simpa only [d911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6882 p hg
    simpa only [d911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6884 (p : Pattern) (guard : d4148 p = 1) : d211 p ≤ (2 : Int) + d132 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6163 p hg
    simpa only [d4148, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6850 p hg
    simpa only [d4148, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6885 (p : Pattern) (guard : d4672 p = 1) : d212 p ≤ (2 : Int) + d132 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6800 p hg
    simpa only [d4672, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6884 p hg
    simpa only [d4672, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6886 (p : Pattern) (guard : d0 p = 1) : d451 p ≤ (2 : Int) + d861 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6887 (p : Pattern) (guard : d4673 p = 1) : d912 p ≤ (2 : Int) + d4700 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d912, d4700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6885 p hg
    simpa only [d4673, d912, d4700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d912, d4700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6886 p hg
    simpa only [d4673, d912, d4700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6888 (p : Pattern) (guard : d4673 p = 1) : d913 p ≤ (2 : Int) + d4702 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d913, d4702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6887 p hg
    simpa only [d913, d4702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d913, d4702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6812 p hg
    simpa only [d913, d4702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6889 (p : Pattern) (guard : d4673 p = 1) : d914 p ≤ (2 : Int) + d4703 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d914, d4703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6799 p hg
    simpa only [d914, d4703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d914, d4703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6888 p hg
    simpa only [d914, d4703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6890 (p : Pattern) (guard : d4673 p = 1) : d915 p ≤ (2 : Int) + d4707 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d915, d4707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6885 p hg
    simpa only [d4673, d915, d4707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d915, d4707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6823 p hg
    simpa only [d4673, d915, d4707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6891 (p : Pattern) (guard : d4673 p = 1) : d916 p ≤ (2 : Int) + d4709 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d916, d4709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6890 p hg
    simpa only [d916, d4709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d916, d4709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6828 p hg
    simpa only [d916, d4709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6892 (p : Pattern) (guard : d4673 p = 1) : d917 p ≤ (2 : Int) + d4710 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d917, d4710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6822 p hg
    simpa only [d917, d4710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d917, d4710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6891 p hg
    simpa only [d917, d4710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6893 (p : Pattern) (guard : d4673 p = 1) : d918 p ≤ (2 : Int) + d4711 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d918, d4711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6889 p hg
    simpa only [d918, d4711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d918, d4711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6892 p hg
    simpa only [d918, d4711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6894 (p : Pattern) (guard : d4673 p = 1) : d919 p ≤ (2 : Int) + d4710 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d919, d4710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6834 p hg
    simpa only [d919, d4710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d919, d4710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6891 p hg
    simpa only [d919, d4710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6895 (p : Pattern) (guard : d4673 p = 1) : d920 p ≤ (2 : Int) + d4712 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d920, d4712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6894 p hg
    simpa only [d920, d4712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d920, d4712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6840 p hg
    simpa only [d920, d4712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6896 (p : Pattern) (guard : d4673 p = 1) : d921 p ≤ (2 : Int) + d4713 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d921, d4713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6893 p hg
    simpa only [d921, d4713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d921, d4713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6895 p hg
    simpa only [d921, d4713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6897 (p : Pattern) (guard : d0 p = 1) : d403 p ≤ (2 : Int) + d269 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6898 (p : Pattern) (guard : d4673 p = 1) : d884 p ≤ (2 : Int) + d4716 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d884, d4716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6789 p hg
    simpa only [d4673, d884, d4716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d884, d4716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6897 p hg
    simpa only [d4673, d884, d4716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6899 (p : Pattern) (guard : d0 p = 1) : d269 p ≤ (2 : Int) + d269 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6900 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (2 : Int) + d268 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2159 p hg
    simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2186 p hg
    simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6901 (p : Pattern) (guard : d1 p = 1) : d132 p ≤ (2 : Int) + d269 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d132, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6900 p hg
    simpa only [d132, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d132, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2161 p hg
    simpa only [d132, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6902 (p : Pattern) (guard : d0 p = 1) : d148 p ≤ (2 : Int) + d269 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6903 (p : Pattern) (guard : d4148 p = 1) : d149 p ≤ (2 : Int) + d269 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6901 p hg
    simpa only [d4148, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6902 p hg
    simpa only [d4148, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6904 (p : Pattern) (guard : d4672 p = 1) : d922 p ≤ (2 : Int) + d269 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6899 p hg
    simpa only [d4672, d922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6903 p hg
    simpa only [d4672, d922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6905 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d274 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6906 (p : Pattern) (guard : d4673 p = 1) : d923 p ≤ (2 : Int) + d4717 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d923, d4717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6904 p hg
    simpa only [d4673, d923, d4717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d923, d4717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6905 p hg
    simpa only [d4673, d923, d4717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6907 (p : Pattern) (guard : d4673 p = 1) : d924 p ≤ (2 : Int) + d4718 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d924, d4718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6898 p hg
    simpa only [d924, d4718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d924, d4718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6906 p hg
    simpa only [d924, d4718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6908 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d298 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6909 (p : Pattern) (guard : d4673 p = 1) : d915 p ≤ (2 : Int) + d4719 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d915, d4719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6885 p hg
    simpa only [d4673, d915, d4719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d915, d4719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6908 p hg
    simpa only [d4673, d915, d4719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6910 (p : Pattern) (guard : d0 p = 1) : d925 p ≤ (2 : Int) + d298 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6911 (p : Pattern) (guard : d1 p = 1) : d273 p ≤ (2 : Int) + d282 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d273, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2189 p hg
    simpa only [d273, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d273, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2170 p hg
    simpa only [d273, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6912 (p : Pattern) (guard : d1 p = 1) : d292 p ≤ (2 : Int) + d298 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d292, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6911 p hg
    simpa only [d292, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d292, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2203 p hg
    simpa only [d292, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6913 (p : Pattern) (guard : d4148 p = 1) : d300 p ≤ (2 : Int) + d298 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6912 p hg
    simpa only [d4148, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6908 p hg
    simpa only [d4148, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6914 (p : Pattern) (guard : d4672 p = 1) : d926 p ≤ (2 : Int) + d298 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6910 p hg
    simpa only [d4672, d926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6913 p hg
    simpa only [d4672, d926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6915 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d1127 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6916 (p : Pattern) (guard : d4673 p = 1) : d927 p ≤ (2 : Int) + d4720 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d927, d4720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6914 p hg
    simpa only [d4673, d927, d4720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d927, d4720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6915 p hg
    simpa only [d4673, d927, d4720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6917 (p : Pattern) (guard : d4673 p = 1) : d928 p ≤ (2 : Int) + d4721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d928, d4721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6909 p hg
    simpa only [d928, d4721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d928, d4721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6916 p hg
    simpa only [d928, d4721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6918 (p : Pattern) (guard : d4673 p = 1) : d929 p ≤ (2 : Int) + d4722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d929, d4722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6907 p hg
    simpa only [d929, d4722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d929, d4722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6917 p hg
    simpa only [d929, d4722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6919 (p : Pattern) (guard : d0 p = 1) : d62 p ≤ (2 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6920 (p : Pattern) (guard : d4148 p = 1) : d241 p ≤ (2 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4806 p hg
    simpa only [d4148, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6919 p hg
    simpa only [d4148, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6921 (p : Pattern) (guard : d4672 p = 1) : d242 p ≤ (2 : Int) + d105 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6786 p hg
    simpa only [d4672, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6920 p hg
    simpa only [d4672, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6922 (p : Pattern) (guard : d4673 p = 1) : d930 p ≤ (2 : Int) + d4704 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d930, d4704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6921 p hg
    simpa only [d4673, d930, d4704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d930, d4704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6850 p hg
    simpa only [d4673, d930, d4704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6923 (p : Pattern) (guard : d4672 p = 1) : d245 p ≤ (2 : Int) + d132 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6817 p hg
    simpa only [d4672, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6884 p hg
    simpa only [d4672, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6924 (p : Pattern) (guard : d4673 p = 1) : d931 p ≤ (2 : Int) + d4705 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d931, d4705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6923 p hg
    simpa only [d4673, d931, d4705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d931, d4705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4673, d931, d4705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6925 (p : Pattern) (guard : d4673 p = 1) : d932 p ≤ (2 : Int) + d4706 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d932, d4706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6922 p hg
    simpa only [d932, d4706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d932, d4706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6924 p hg
    simpa only [d932, d4706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6926 (p : Pattern) (guard : d4673 p = 1) : d931 p ≤ (2 : Int) + d4707 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d931, d4707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6923 p hg
    simpa only [d4673, d931, d4707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d931, d4707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6823 p hg
    simpa only [d4673, d931, d4707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6927 (p : Pattern) (guard : d0 p = 1) : d109 p ≤ (2 : Int) + d109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6928 (p : Pattern) (guard : d4672 p = 1) : d933 p ≤ (2 : Int) + d109 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6927 p hg
    simpa only [d4672, d933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6826 p hg
    simpa only [d4672, d933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6929 (p : Pattern) (guard : d4673 p = 1) : d934 p ≤ (2 : Int) + d4708 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d934, d4708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6928 p hg
    simpa only [d4673, d934, d4708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d934, d4708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4673, d934, d4708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6930 (p : Pattern) (guard : d4673 p = 1) : d935 p ≤ (2 : Int) + d4709 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d935, d4709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6926 p hg
    simpa only [d935, d4709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d935, d4709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6929 p hg
    simpa only [d935, d4709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6931 (p : Pattern) (guard : d4673 p = 1) : d936 p ≤ (2 : Int) + d4710 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d936, d4710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6925 p hg
    simpa only [d936, d4710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d936, d4710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6930 p hg
    simpa only [d936, d4710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6932 (p : Pattern) (guard : d4673 p = 1) : d937 p ≤ (2 : Int) + d4723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d937, d4723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6918 p hg
    simpa only [d937, d4723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d937, d4723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6931 p hg
    simpa only [d937, d4723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6933 (p : Pattern) (guard : d0 p = 1) : d26 p ≤ (2 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6934 (p : Pattern) (guard : d4148 p = 1) : d252 p ≤ (2 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4806 p hg
    simpa only [d4148, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6933 p hg
    simpa only [d4148, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6935 (p : Pattern) (guard : d4672 p = 1) : d253 p ≤ (2 : Int) + d105 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6786 p hg
    simpa only [d4672, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6934 p hg
    simpa only [d4672, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6936 (p : Pattern) (guard : d4673 p = 1) : d938 p ≤ (2 : Int) + d4704 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d938, d4704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6935 p hg
    simpa only [d4673, d938, d4704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d938, d4704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6850 p hg
    simpa only [d4673, d938, d4704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6937 (p : Pattern) (guard : d0 p = 1) : d62 p ≤ (2 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6938 (p : Pattern) (guard : d4148 p = 1) : d136 p ≤ (2 : Int) + d132 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6163 p hg
    simpa only [d4148, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6937 p hg
    simpa only [d4148, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6939 (p : Pattern) (guard : d4672 p = 1) : d939 p ≤ (2 : Int) + d132 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6817 p hg
    simpa only [d4672, d939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6938 p hg
    simpa only [d4672, d939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6940 (p : Pattern) (guard : d4673 p = 1) : d940 p ≤ (2 : Int) + d4705 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d940, d4705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6939 p hg
    simpa only [d4673, d940, d4705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d940, d4705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4673, d940, d4705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6941 (p : Pattern) (guard : d4673 p = 1) : d941 p ≤ (2 : Int) + d4706 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d941, d4706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6936 p hg
    simpa only [d941, d4706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d941, d4706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6940 p hg
    simpa only [d941, d4706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6942 (p : Pattern) (guard : d4673 p = 1) : d942 p ≤ (2 : Int) + d4710 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d942, d4710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6941 p hg
    simpa only [d942, d4710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d942, d4710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6930 p hg
    simpa only [d942, d4710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6943 (p : Pattern) (guard : d4673 p = 1) : d943 p ≤ (2 : Int) + d4712 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d943, d4712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6942 p hg
    simpa only [d943, d4712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d943, d4712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6739 p hg
    simpa only [d943, d4712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6944 (p : Pattern) (guard : d4673 p = 1) : d944 p ≤ (2 : Int) + d4724 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d944, d4724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6932 p hg
    simpa only [d944, d4724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d944, d4724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6943 p hg
    simpa only [d944, d4724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6945 (p : Pattern) (guard : d4673 p = 1) : d945 p ≤ (2 : Int) + d4725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d945, d4725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6896 p hg
    simpa only [d945, d4725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d945, d4725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6944 p hg
    simpa only [d945, d4725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6946 (p : Pattern) (guard : d4673 p = 1) : d946 p ≤ (2 : Int) + d4726 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d946, d4726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6760 p hg
    simpa only [d946, d4726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d946, d4726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6945 p hg
    simpa only [d946, d4726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6947 (p : Pattern) (guard : d4673 p = 1) : d947 p ≤ (2 : Int) + d4727 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d947, d4727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6883 p hg
    simpa only [d947, d4727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d947, d4727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6946 p hg
    simpa only [d947, d4727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6948 (p : Pattern) (guard : d4673 p = 1) : d948 p ≤ (2 : Int) + d4728 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d948, d4728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6859 p hg
    simpa only [d948, d4728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d948, d4728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6947 p hg
    simpa only [d948, d4728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6949 (p : Pattern) (guard : d0 p = 1) : d362 p ≤ (0 : Int) + d28 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6950 (p : Pattern) (guard : d4299 p = 1) : d790 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d790, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3199 p hg
    simpa only [d4299, d790, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d790, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6949 p hg
    simpa only [d4299, d790, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6951 (p : Pattern) (guard : d0 p = 1) : d792 p ≤ (0 : Int) + d376 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6952 (p : Pattern) (guard : d4301 p = 1) : d793 p ≤ (0 : Int) + d710 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d793, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6950 p hg
    simpa only [d4301, d793, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d793, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6951 p hg
    simpa only [d4301, d793, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6953 (p : Pattern) (guard : d0 p = 1) : d387 p ≤ (0 : Int) + d64 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6954 (p : Pattern) (guard : d4299 p = 1) : d794 p ≤ (0 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d794, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3204 p hg
    simpa only [d4299, d794, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d794, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6953 p hg
    simpa only [d4299, d794, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6955 (p : Pattern) (guard : d0 p = 1) : d800 p ≤ (0 : Int) + d391 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6956 (p : Pattern) (guard : d4301 p = 1) : d801 p ≤ (0 : Int) + d711 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d801, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6954 p hg
    simpa only [d4301, d801, d711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d801, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6955 p hg
    simpa only [d4301, d801, d711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6957 (p : Pattern) (guard : d4301 p = 1) : d802 p ≤ (0 : Int) + d712 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d802, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6952 p hg
    simpa only [d802, d712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d802, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6956 p hg
    simpa only [d802, d712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6958 (p : Pattern) (guard : d0 p = 1) : d394 p ≤ (0 : Int) + d28 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6959 (p : Pattern) (guard : d4299 p = 1) : d803 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d803, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3199 p hg
    simpa only [d4299, d803, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d803, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6958 p hg
    simpa only [d4299, d803, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6960 (p : Pattern) (guard : d0 p = 1) : d805 p ≤ (0 : Int) + d396 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6961 (p : Pattern) (guard : d4301 p = 1) : d806 p ≤ (0 : Int) + d713 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d806, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6959 p hg
    simpa only [d4301, d806, d713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d806, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6960 p hg
    simpa only [d4301, d806, d713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6962 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d64 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6963 (p : Pattern) (guard : d4299 p = 1) : d807 p ≤ (0 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d807, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3204 p hg
    simpa only [d4299, d807, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d807, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6962 p hg
    simpa only [d4299, d807, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6964 (p : Pattern) (guard : d0 p = 1) : d811 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6965 (p : Pattern) (guard : d4301 p = 1) : d812 p ≤ (0 : Int) + d714 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d812, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6963 p hg
    simpa only [d4301, d812, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d812, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6964 p hg
    simpa only [d4301, d812, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6966 (p : Pattern) (guard : d4301 p = 1) : d813 p ≤ (0 : Int) + d715 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d813, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6961 p hg
    simpa only [d813, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d813, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6965 p hg
    simpa only [d813, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6967 (p : Pattern) (guard : d4301 p = 1) : d814 p ≤ (0 : Int) + d716 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d814, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6957 p hg
    simpa only [d814, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d814, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6966 p hg
    simpa only [d814, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6968 (p : Pattern) (guard : d0 p = 1) : d403 p ≤ (0 : Int) + d28 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6969 (p : Pattern) (guard : d4299 p = 1) : d815 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d815, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3199 p hg
    simpa only [d4299, d815, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d815, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6968 p hg
    simpa only [d4299, d815, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6970 (p : Pattern) (guard : d0 p = 1) : d805 p ≤ (0 : Int) + d405 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6971 (p : Pattern) (guard : d4301 p = 1) : d816 p ≤ (0 : Int) + d717 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d816, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6969 p hg
    simpa only [d4301, d816, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d816, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6970 p hg
    simpa only [d4301, d816, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6972 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (0 : Int) + d64 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6973 (p : Pattern) (guard : d4299 p = 1) : d817 p ≤ (0 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d817, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3204 p hg
    simpa only [d4299, d817, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d817, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6972 p hg
    simpa only [d4299, d817, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6974 (p : Pattern) (guard : d4301 p = 1) : d818 p ≤ (0 : Int) + d714 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d818, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6973 p hg
    simpa only [d4301, d818, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d818, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6964 p hg
    simpa only [d4301, d818, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6975 (p : Pattern) (guard : d4301 p = 1) : d819 p ≤ (0 : Int) + d718 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d819, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6971 p hg
    simpa only [d819, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d819, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6974 p hg
    simpa only [d819, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6976 (p : Pattern) (guard : d4299 p = 1) : d820 p ≤ (0 : Int) + d92 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d820, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5893 p hg
    simpa only [d4299, d820, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d820, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6449 p hg
    simpa only [d4299, d820, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6977 (p : Pattern) (guard : d4301 p = 1) : d821 p ≤ (0 : Int) + d719 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d821, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6976 p hg
    simpa only [d4301, d821, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d821, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4608 p hg
    simpa only [d4301, d821, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6978 (p : Pattern) (guard : d4301 p = 1) : d822 p ≤ (0 : Int) + d720 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d822, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6977 p hg
    simpa only [d822, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d822, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5898 p hg
    simpa only [d822, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6979 (p : Pattern) (guard : d4301 p = 1) : d823 p ≤ (0 : Int) + d721 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d823, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6975 p hg
    simpa only [d823, d721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d823, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6978 p hg
    simpa only [d823, d721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6980 (p : Pattern) (guard : d4301 p = 1) : d824 p ≤ (0 : Int) + d722 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d824, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6967 p hg
    simpa only [d824, d722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d824, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6979 p hg
    simpa only [d824, d722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6981 (p : Pattern) (guard : d0 p = 1) : d390 p ≤ (0 : Int) + d28 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6982 (p : Pattern) (guard : d4299 p = 1) : d825 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d825, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3199 p hg
    simpa only [d4299, d825, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d825, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6981 p hg
    simpa only [d4299, d825, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6983 (p : Pattern) (guard : d0 p = 1) : d826 p ≤ (0 : Int) + d409 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6984 (p : Pattern) (guard : d4301 p = 1) : d827 p ≤ (0 : Int) + d723 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d827, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6982 p hg
    simpa only [d4301, d827, d723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d827, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6983 p hg
    simpa only [d4301, d827, d723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6985 (p : Pattern) (guard : d0 p = 1) : d394 p ≤ (0 : Int) + d64 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6986 (p : Pattern) (guard : d4299 p = 1) : d828 p ≤ (0 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d828, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3204 p hg
    simpa only [d4299, d828, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d828, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6985 p hg
    simpa only [d4299, d828, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6987 (p : Pattern) (guard : d0 p = 1) : d800 p ≤ (0 : Int) + d396 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6988 (p : Pattern) (guard : d4301 p = 1) : d829 p ≤ (0 : Int) + d724 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d829, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6986 p hg
    simpa only [d4301, d829, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d829, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6987 p hg
    simpa only [d4301, d829, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6989 (p : Pattern) (guard : d4301 p = 1) : d830 p ≤ (0 : Int) + d725 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d830, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6984 p hg
    simpa only [d830, d725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d830, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6988 p hg
    simpa only [d830, d725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6990 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d28 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6991 (p : Pattern) (guard : d4299 p = 1) : d831 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d831, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3199 p hg
    simpa only [d4299, d831, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d831, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6990 p hg
    simpa only [d4299, d831, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6992 (p : Pattern) (guard : d0 p = 1) : d805 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6993 (p : Pattern) (guard : d4301 p = 1) : d832 p ≤ (0 : Int) + d726 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d832, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6991 p hg
    simpa only [d4301, d832, d726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d832, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6992 p hg
    simpa only [d4301, d832, d726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6994 (p : Pattern) (guard : d4301 p = 1) : d833 p ≤ (0 : Int) + d727 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d833, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6993 p hg
    simpa only [d833, d727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d833, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6965 p hg
    simpa only [d833, d727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6995 (p : Pattern) (guard : d4301 p = 1) : d834 p ≤ (0 : Int) + d728 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d834, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6989 p hg
    simpa only [d834, d728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d834, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6994 p hg
    simpa only [d834, d728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6996 (p : Pattern) (guard : d4301 p = 1) : d835 p ≤ (0 : Int) + d729 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d835, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6994 p hg
    simpa only [d835, d729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d835, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5911 p hg
    simpa only [d835, d729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6997 (p : Pattern) (guard : d4301 p = 1) : d836 p ≤ (0 : Int) + d730 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d836, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6995 p hg
    simpa only [d836, d730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d836, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6996 p hg
    simpa only [d836, d730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6998 (p : Pattern) (guard : d4301 p = 1) : d837 p ≤ (0 : Int) + d731 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d837, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6980 p hg
    simpa only [d837, d731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d837, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6997 p hg
    simpa only [d837, d731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6999 (p : Pattern) (guard : d0 p = 1) : d372 p ≤ (0 : Int) + d28 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
