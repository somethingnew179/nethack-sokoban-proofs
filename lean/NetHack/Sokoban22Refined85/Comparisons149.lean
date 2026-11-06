/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons148
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare20860 (p : Pattern) (guard : d5850 p = 1) : d2680 p ≤ (0 : Int) + d3819 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2680, d3819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20789 p hg
    simpa only [d2680, d3819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2680, d3819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20859 p hg
    simpa only [d2680, d3819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20861 (p : Pattern) (guard : d5850 p = 1) : d2686 p ≤ (0 : Int) + d3820 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2686, d3820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20751 p hg
    simpa only [d2686, d3820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2686, d3820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20860 p hg
    simpa only [d2686, d3820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20862 (p : Pattern) (guard : d5850 p = 1) : d2745 p ≤ (0 : Int) + d3821 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2745, d3821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20757 p hg
    simpa only [d2745, d3821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2745, d3821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2745, d3821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20863 (p : Pattern) (guard : d5850 p = 1) : d2746 p ≤ (0 : Int) + d3822 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2746, d3822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20861 p hg
    simpa only [d2746, d3822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2746, d3822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20862 p hg
    simpa only [d2746, d3822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20864 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3823 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20865 (p : Pattern) (guard : d5850 p = 1) : d2679 p ≤ (0 : Int) + d3824 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2679, d3824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20755 p hg
    simpa only [d5850, d2679, d3824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2679, d3824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20864 p hg
    simpa only [d5850, d2679, d3824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20866 (p : Pattern) (guard : d5850 p = 1) : d2680 p ≤ (0 : Int) + d3825 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2680, d3825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20789 p hg
    simpa only [d2680, d3825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2680, d3825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20865 p hg
    simpa only [d2680, d3825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20867 (p : Pattern) (guard : d5850 p = 1) : d2745 p ≤ (0 : Int) + d3826 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2745, d3826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20866 p hg
    simpa only [d2745, d3826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2745, d3826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2745, d3826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20868 (p : Pattern) (guard : d5850 p = 1) : d2746 p ≤ (0 : Int) + d3827 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2746, d3827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20793 p hg
    simpa only [d2746, d3827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2746, d3827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20867 p hg
    simpa only [d2746, d3827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20869 (p : Pattern) (guard : d5850 p = 1) : d2746 p ≤ (0 : Int) + d3828 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20863 p hg
    simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20868 p hg
    simpa only [d3828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20870 (p : Pattern) (guard : d5850 p = 1) : d2745 p ≤ (0 : Int) + d3829 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2745, d3829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20792 p hg
    simpa only [d2745, d3829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2745, d3829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2745, d3829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20871 (p : Pattern) (guard : d5850 p = 1) : d2746 p ≤ (0 : Int) + d3830 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2746, d3830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20793 p hg
    simpa only [d2746, d3830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2746, d3830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20870 p hg
    simpa only [d2746, d3830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20872 (p : Pattern) (guard : d5850 p = 1) : d2747 p ≤ (0 : Int) + d3831 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2747, d3831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20817 p hg
    simpa only [d2747, d3831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2747, d3831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2747, d3831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20873 (p : Pattern) (guard : d5850 p = 1) : d2748 p ≤ (0 : Int) + d3832 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2748, d3832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20818 p hg
    simpa only [d2748, d3832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2748, d3832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20872 p hg
    simpa only [d2748, d3832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20874 (p : Pattern) (guard : d5850 p = 1) : d2749 p ≤ (0 : Int) + d3833 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2749, d3833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20871 p hg
    simpa only [d2749, d3833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2749, d3833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20873 p hg
    simpa only [d2749, d3833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20875 (p : Pattern) (guard : d5850 p = 1) : d2750 p ≤ (0 : Int) + d3834 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2750, d3834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20869 p hg
    simpa only [d2750, d3834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2750, d3834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20874 p hg
    simpa only [d2750, d3834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20876 (p : Pattern) (guard : d5850 p = 1) : d2751 p ≤ (0 : Int) + d3835 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2751, d3835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20874 p hg
    simpa only [d2751, d3835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2751, d3835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20785 p hg
    simpa only [d2751, d3835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20877 (p : Pattern) (guard : d5850 p = 1) : d2752 p ≤ (0 : Int) + d3836 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2752, d3836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20875 p hg
    simpa only [d2752, d3836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2752, d3836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20876 p hg
    simpa only [d2752, d3836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20878 (p : Pattern) (guard : d5850 p = 1) : d2753 p ≤ (0 : Int) + d3837 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2753, d3837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20849 p hg
    simpa only [d2753, d3837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2753, d3837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20801 p hg
    simpa only [d2753, d3837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20879 (p : Pattern) (guard : d5850 p = 1) : d2707 p ≤ (0 : Int) + d119 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20210 p hg
    simpa only [d5850, d2707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20290 p hg
    simpa only [d5850, d2707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20880 (p : Pattern) (guard : d5850 p = 1) : d2754 p ≤ (0 : Int) + d3838 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2754, d3838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20879 p hg
    simpa only [d2754, d3838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2754, d3838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20808 p hg
    simpa only [d2754, d3838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20881 (p : Pattern) (guard : d5850 p = 1) : d2755 p ≤ (0 : Int) + d3839 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2755, d3839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20880 p hg
    simpa only [d2755, d3839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2755, d3839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20809 p hg
    simpa only [d2755, d3839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20882 (p : Pattern) (guard : d5850 p = 1) : d2756 p ≤ (0 : Int) + d3840 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2756, d3840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20878 p hg
    simpa only [d2756, d3840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2756, d3840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20881 p hg
    simpa only [d2756, d3840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20883 (p : Pattern) (guard : d5850 p = 1) : d2757 p ≤ (0 : Int) + d3841 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2757, d3841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20882 p hg
    simpa only [d2757, d3841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2757, d3841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2757, d3841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20884 (p : Pattern) (guard : d5850 p = 1) : d2758 p ≤ (0 : Int) + d3842 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2758, d3842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20883 p hg
    simpa only [d2758, d3842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2758, d3842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2758, d3842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20885 (p : Pattern) (guard : d5850 p = 1) : d2759 p ≤ (0 : Int) + d3843 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2759, d3843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20877 p hg
    simpa only [d2759, d3843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2759, d3843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20884 p hg
    simpa only [d2759, d3843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20886 (p : Pattern) (guard : d5850 p = 1) : d2760 p ≤ (0 : Int) + d3844 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2760, d3844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20868 p hg
    simpa only [d2760, d3844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2760, d3844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20878 p hg
    simpa only [d2760, d3844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20887 (p : Pattern) (guard : d5850 p = 1) : d2761 p ≤ (0 : Int) + d3845 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2761, d3845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20873 p hg
    simpa only [d2761, d3845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2761, d3845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20639 p hg
    simpa only [d2761, d3845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20888 (p : Pattern) (guard : d5850 p = 1) : d2762 p ≤ (0 : Int) + d3846 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2762, d3846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20886 p hg
    simpa only [d2762, d3846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2762, d3846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20887 p hg
    simpa only [d2762, d3846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20889 (p : Pattern) (guard : d5850 p = 1) : d2763 p ≤ (0 : Int) + d3847 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2763, d3847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20873 p hg
    simpa only [d2763, d3847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2763, d3847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20643 p hg
    simpa only [d2763, d3847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20890 (p : Pattern) (guard : d5850 p = 1) : d2764 p ≤ (0 : Int) + d3848 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2764, d3848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20889 p hg
    simpa only [d2764, d3848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2764, d3848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2764, d3848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20891 (p : Pattern) (guard : d5850 p = 1) : d2765 p ≤ (0 : Int) + d3849 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2765, d3849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20888 p hg
    simpa only [d2765, d3849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2765, d3849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20890 p hg
    simpa only [d2765, d3849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20892 (p : Pattern) (guard : d5850 p = 1) : d2766 p ≤ (0 : Int) + d3850 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2766, d3850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20881 p hg
    simpa only [d2766, d3850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2766, d3850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2766, d3850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20893 (p : Pattern) (guard : d5850 p = 1) : d2767 p ≤ (0 : Int) + d3851 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2767, d3851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20892 p hg
    simpa only [d2767, d3851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2767, d3851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2767, d3851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20894 (p : Pattern) (guard : d5850 p = 1) : d2768 p ≤ (0 : Int) + d3852 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2768, d3852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20893 p hg
    simpa only [d2768, d3852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2768, d3852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2768, d3852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20895 (p : Pattern) (guard : d5850 p = 1) : d2769 p ≤ (0 : Int) + d3853 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2769, d3853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20891 p hg
    simpa only [d2769, d3853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2769, d3853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20894 p hg
    simpa only [d2769, d3853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20896 (p : Pattern) (guard : d5850 p = 1) : d2770 p ≤ (0 : Int) + d3854 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2770, d3854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20885 p hg
    simpa only [d2770, d3854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2770, d3854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20895 p hg
    simpa only [d2770, d3854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20897 (p : Pattern) (guard : d5850 p = 1) : d2771 p ≤ (0 : Int) + d3855 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2771, d3855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20858 p hg
    simpa only [d2771, d3855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2771, d3855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20896 p hg
    simpa only [d2771, d3855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20898 (p : Pattern) (guard : d5850 p = 1) : d2772 p ≤ (0 : Int) + d3856 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2772, d3856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20785 p hg
    simpa only [d2772, d3856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2772, d3856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2772, d3856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20899 (p : Pattern) (guard : d5850 p = 1) : d2773 p ≤ (0 : Int) + d3857 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2773, d3857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20898 p hg
    simpa only [d2773, d3857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2773, d3857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2773, d3857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20900 (p : Pattern) (guard : d5850 p = 1) : d2774 p ≤ (0 : Int) + d3858 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2774, d3858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20899 p hg
    simpa only [d2774, d3858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2774, d3858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2774, d3858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20901 (p : Pattern) (guard : d5850 p = 1) : d2775 p ≤ (0 : Int) + d3859 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2775, d3859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20900 p hg
    simpa only [d2775, d3859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2775, d3859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2775, d3859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20902 (p : Pattern) (guard : d5850 p = 1) : d2776 p ≤ (0 : Int) + d3860 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2776, d3860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20896 p hg
    simpa only [d2776, d3860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2776, d3860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20901 p hg
    simpa only [d2776, d3860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20903 (p : Pattern) (guard : d5850 p = 1) : d2777 p ≤ (0 : Int) + d3861 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2777, d3861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20897 p hg
    simpa only [d2777, d3861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2777, d3861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20902 p hg
    simpa only [d2777, d3861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20904 (p : Pattern) (guard : d5850 p = 1) : d2778 p ≤ (0 : Int) + d3862 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2778, d3862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20767 p hg
    simpa only [d2778, d3862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2778, d3862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20783 p hg
    simpa only [d2778, d3862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20905 (p : Pattern) (guard : d5850 p = 1) : d2779 p ≤ (0 : Int) + d3863 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2779, d3863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20904 p hg
    simpa only [d2779, d3863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2779, d3863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20786 p hg
    simpa only [d2779, d3863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20906 (p : Pattern) (guard : d5850 p = 1) : d2780 p ≤ (0 : Int) + d3864 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2780, d3864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20905 p hg
    simpa only [d2780, d3864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2780, d3864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20824 p hg
    simpa only [d2780, d3864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20907 (p : Pattern) (guard : d5850 p = 1) : d2781 p ≤ (0 : Int) + d3802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2781, d3802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20767 p hg
    simpa only [d2781, d3802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2781, d3802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20842 p hg
    simpa only [d2781, d3802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20908 (p : Pattern) (guard : d5850 p = 1) : d2782 p ≤ (0 : Int) + d3804 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2782, d3804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20907 p hg
    simpa only [d2782, d3804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2782, d3804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20844 p hg
    simpa only [d2782, d3804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20909 (p : Pattern) (guard : d5850 p = 1) : d2783 p ≤ (0 : Int) + d3807 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2783, d3807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20908 p hg
    simpa only [d2783, d3807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2783, d3807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20847 p hg
    simpa only [d2783, d3807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20910 (p : Pattern) (guard : d5850 p = 1) : d2784 p ≤ (0 : Int) + d3816 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2784, d3816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20909 p hg
    simpa only [d2784, d3816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2784, d3816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20856 p hg
    simpa only [d2784, d3816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20911 (p : Pattern) (guard : d5850 p = 1) : d2785 p ≤ (0 : Int) + d3865 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2785, d3865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20906 p hg
    simpa only [d2785, d3865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2785, d3865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20910 p hg
    simpa only [d2785, d3865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20912 (p : Pattern) (guard : d5850 p = 1) : d2786 p ≤ (0 : Int) + d3866 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2786, d3866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20911 p hg
    simpa only [d2786, d3866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2786, d3866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20896 p hg
    simpa only [d2786, d3866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20913 (p : Pattern) (guard : d5850 p = 1) : d2787 p ≤ (0 : Int) + d3867 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2787, d3867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20896 p hg
    simpa only [d2787, d3867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2787, d3867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2787, d3867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20914 (p : Pattern) (guard : d5850 p = 1) : d2788 p ≤ (0 : Int) + d3868 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2788, d3868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20912 p hg
    simpa only [d2788, d3868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2788, d3868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20913 p hg
    simpa only [d2788, d3868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20915 (p : Pattern) (guard : d5850 p = 1) : d2789 p ≤ (0 : Int) + d3869 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2789, d3869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20903 p hg
    simpa only [d2789, d3869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2789, d3869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20914 p hg
    simpa only [d2789, d3869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20916 (p : Pattern) (guard : d5850 p = 1) : d2790 p ≤ (0 : Int) + d3870 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2790, d3870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20724 p hg
    simpa only [d2790, d3870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2790, d3870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20915 p hg
    simpa only [d2790, d3870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20917 (p : Pattern) (guard : d5850 p = 1) : d2791 p ≤ (0 : Int) + d3871 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2791, d3871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20748 p hg
    simpa only [d2791, d3871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2791, d3871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20916 p hg
    simpa only [d2791, d3871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20918 (p : Pattern) (guard : d5850 p = 1) : d2521 p ≤ (0 : Int) + d3872 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2521, d3872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20537 p hg
    simpa only [d5850, d2521, d3872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2521, d3872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20596 p hg
    simpa only [d5850, d2521, d3872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20919 (p : Pattern) (guard : d5850 p = 1) : d2522 p ≤ (0 : Int) + d3873 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2522, d3873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20597 p hg
    simpa only [d2522, d3873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2522, d3873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20918 p hg
    simpa only [d2522, d3873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20920 (p : Pattern) (guard : d5850 p = 1) : d2523 p ≤ (0 : Int) + d3874 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2523, d3874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20534 p hg
    simpa only [d2523, d3874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2523, d3874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20919 p hg
    simpa only [d2523, d3874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20921 (p : Pattern) (guard : d5850 p = 1) : d2602 p ≤ (0 : Int) + d3875 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2602, d3875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20539 p hg
    simpa only [d2602, d3875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2602, d3875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2602, d3875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20922 (p : Pattern) (guard : d5850 p = 1) : d2603 p ≤ (0 : Int) + d3876 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2603, d3876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20920 p hg
    simpa only [d2603, d3876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2603, d3876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20921 p hg
    simpa only [d2603, d3876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20923 (p : Pattern) (guard : d5850 p = 1) : d2604 p ≤ (0 : Int) + d3877 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2604, d3877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20664 p hg
    simpa only [d2604, d3877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2604, d3877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20922 p hg
    simpa only [d2604, d3877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20924 (p : Pattern) (guard : d5850 p = 1) : d2605 p ≤ (0 : Int) + d3878 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2605, d3878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20664 p hg
    simpa only [d2605, d3878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2605, d3878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20923 p hg
    simpa only [d2605, d3878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20925 (p : Pattern) (guard : d5850 p = 1) : d2609 p ≤ (0 : Int) + d3879 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2609, d3879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20923 p hg
    simpa only [d2609, d3879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2609, d3879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20679 p hg
    simpa only [d2609, d3879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20926 (p : Pattern) (guard : d5850 p = 1) : d2610 p ≤ (0 : Int) + d3880 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2610, d3880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20924 p hg
    simpa only [d2610, d3880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2610, d3880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20925 p hg
    simpa only [d2610, d3880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20927 (p : Pattern) (guard : d5850 p = 1) : d2792 p ≤ (0 : Int) + d3881 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2792, d3881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20647 p hg
    simpa only [d2792, d3881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2792, d3881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20587 p hg
    simpa only [d2792, d3881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20928 (p : Pattern) (guard : d5850 p = 1) : d2793 p ≤ (0 : Int) + d3882 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2793, d3882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20682 p hg
    simpa only [d2793, d3882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2793, d3882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20927 p hg
    simpa only [d2793, d3882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20929 (p : Pattern) (guard : d5850 p = 1) : d2794 p ≤ (0 : Int) + d3883 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2794, d3883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20647 p hg
    simpa only [d2794, d3883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2794, d3883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20594 p hg
    simpa only [d2794, d3883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20930 (p : Pattern) (guard : d5850 p = 1) : d2795 p ≤ (0 : Int) + d3884 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2795, d3884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20684 p hg
    simpa only [d2795, d3884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2795, d3884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2795, d3884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20931 (p : Pattern) (guard : d5850 p = 1) : d2796 p ≤ (0 : Int) + d3885 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2796, d3885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20929 p hg
    simpa only [d2796, d3885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2796, d3885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20930 p hg
    simpa only [d2796, d3885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20932 (p : Pattern) (guard : d5850 p = 1) : d2797 p ≤ (0 : Int) + d3886 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2797, d3886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20928 p hg
    simpa only [d2797, d3886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2797, d3886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20931 p hg
    simpa only [d2797, d3886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20933 (p : Pattern) (guard : d5850 p = 1) : d2798 p ≤ (0 : Int) + d3887 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2798, d3887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20648 p hg
    simpa only [d2798, d3887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2798, d3887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20930 p hg
    simpa only [d2798, d3887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20934 (p : Pattern) (guard : d5850 p = 1) : d2799 p ≤ (0 : Int) + d3888 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2799, d3888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20933 p hg
    simpa only [d2799, d3888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2799, d3888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20655 p hg
    simpa only [d2799, d3888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20935 (p : Pattern) (guard : d5850 p = 1) : d2800 p ≤ (0 : Int) + d3889 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2800, d3889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20932 p hg
    simpa only [d2800, d3889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2800, d3889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20934 p hg
    simpa only [d2800, d3889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20936 (p : Pattern) (guard : d5850 p = 1) : d2801 p ≤ (0 : Int) + d3890 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2801, d3890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20926 p hg
    simpa only [d2801, d3890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2801, d3890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20935 p hg
    simpa only [d2801, d3890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20937 (p : Pattern) (guard : d5850 p = 1) : d2541 p ≤ (0 : Int) + d3891 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2541, d3891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20575 p hg
    simpa only [d5850, d2541, d3891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2541, d3891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20572 p hg
    simpa only [d5850, d2541, d3891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20938 (p : Pattern) (guard : d5850 p = 1) : d2542 p ≤ (0 : Int) + d3892 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2542, d3892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20573 p hg
    simpa only [d2542, d3892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2542, d3892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20937 p hg
    simpa only [d2542, d3892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20939 (p : Pattern) (guard : d5850 p = 1) : d2569 p ≤ (0 : Int) + d3893 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2569, d3893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20617 p hg
    simpa only [d2569, d3893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2569, d3893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20938 p hg
    simpa only [d2569, d3893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20940 (p : Pattern) (guard : d5850 p = 1) : d2543 p ≤ (0 : Int) + d3894 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2543, d3894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20620 p hg
    simpa only [d2543, d3894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2543, d3894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2543, d3894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20941 (p : Pattern) (guard : d5850 p = 1) : d2611 p ≤ (0 : Int) + d3895 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2611, d3895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20939 p hg
    simpa only [d2611, d3895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2611, d3895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20940 p hg
    simpa only [d2611, d3895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20942 (p : Pattern) (guard : d5850 p = 1) : d2618 p ≤ (0 : Int) + d3896 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2618, d3896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20664 p hg
    simpa only [d2618, d3896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2618, d3896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20941 p hg
    simpa only [d2618, d3896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20943 (p : Pattern) (guard : d5850 p = 1) : d2619 p ≤ (0 : Int) + d3897 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2619, d3897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20922 p hg
    simpa only [d2619, d3897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2619, d3897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20678 p hg
    simpa only [d2619, d3897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20944 (p : Pattern) (guard : d5850 p = 1) : d2620 p ≤ (0 : Int) + d3898 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2620, d3898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20942 p hg
    simpa only [d2620, d3898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2620, d3898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20943 p hg
    simpa only [d2620, d3898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20945 (p : Pattern) (guard : d5850 p = 1) : d2621 p ≤ (0 : Int) + d3899 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2621, d3899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20922 p hg
    simpa only [d2621, d3899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2621, d3899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20639 p hg
    simpa only [d2621, d3899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20946 (p : Pattern) (guard : d5850 p = 1) : d2622 p ≤ (0 : Int) + d3900 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2622, d3900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20945 p hg
    simpa only [d2622, d3900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2622, d3900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20644 p hg
    simpa only [d2622, d3900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20947 (p : Pattern) (guard : d5850 p = 1) : d2623 p ≤ (0 : Int) + d3901 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2623, d3901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20944 p hg
    simpa only [d2623, d3901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2623, d3901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20946 p hg
    simpa only [d2623, d3901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20948 (p : Pattern) (guard : d5850 p = 1) : d2802 p ≤ (0 : Int) + d3902 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2802, d3902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20927 p hg
    simpa only [d2802, d3902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2802, d3902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20602 p hg
    simpa only [d2802, d3902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20949 (p : Pattern) (guard : d5850 p = 1) : d2803 p ≤ (0 : Int) + d3903 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2803, d3903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20930 p hg
    simpa only [d2803, d3903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2803, d3903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20654 p hg
    simpa only [d2803, d3903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20950 (p : Pattern) (guard : d5850 p = 1) : d2804 p ≤ (0 : Int) + d3904 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2804, d3904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20948 p hg
    simpa only [d2804, d3904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2804, d3904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20949 p hg
    simpa only [d2804, d3904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20951 (p : Pattern) (guard : d5850 p = 1) : d2805 p ≤ (0 : Int) + d3905 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2805, d3905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20930 p hg
    simpa only [d2805, d3905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2805, d3905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2805, d3905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20952 (p : Pattern) (guard : d5850 p = 1) : d2806 p ≤ (0 : Int) + d3906 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2806, d3906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20951 p hg
    simpa only [d2806, d3906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2806, d3906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2806, d3906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20953 (p : Pattern) (guard : d5850 p = 1) : d2807 p ≤ (0 : Int) + d3907 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2807, d3907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20950 p hg
    simpa only [d2807, d3907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2807, d3907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20952 p hg
    simpa only [d2807, d3907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20954 (p : Pattern) (guard : d5850 p = 1) : d2808 p ≤ (0 : Int) + d3908 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2808, d3908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20947 p hg
    simpa only [d2808, d3908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2808, d3908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20953 p hg
    simpa only [d2808, d3908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20955 (p : Pattern) (guard : d5850 p = 1) : d2809 p ≤ (0 : Int) + d3909 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2809, d3909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20936 p hg
    simpa only [d2809, d3909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2809, d3909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20954 p hg
    simpa only [d2809, d3909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20956 (p : Pattern) (guard : d5850 p = 1) : d2518 p ≤ (0 : Int) + d3910 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2518, d3910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20510 p hg
    simpa only [d2518, d3910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2518, d3910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20667 p hg
    simpa only [d2518, d3910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20957 (p : Pattern) (guard : d5850 p = 1) : d2600 p ≤ (0 : Int) + d3911 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2600, d3911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20661 p hg
    simpa only [d2600, d3911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2600, d3911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2600, d3911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20958 (p : Pattern) (guard : d5850 p = 1) : d2601 p ≤ (0 : Int) + d3912 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2601, d3912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20956 p hg
    simpa only [d2601, d3912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2601, d3912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20957 p hg
    simpa only [d2601, d3912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20959 (p : Pattern) (guard : d5850 p = 1) : d2601 p ≤ (0 : Int) + d3913 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20958 p hg
    simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20672 p hg
    simpa only [d3913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20960 (p : Pattern) (guard : d5850 p = 1) : d2810 p ≤ (0 : Int) + d3914 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2810, d3914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20959 p hg
    simpa only [d2810, d3914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2810, d3914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20686 p hg
    simpa only [d2810, d3914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20961 (p : Pattern) (guard : d5850 p = 1) : d2811 p ≤ (0 : Int) + d3915 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2811, d3915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20960 p hg
    simpa only [d2811, d3915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2811, d3915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20687 p hg
    simpa only [d2811, d3915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20962 (p : Pattern) (guard : d5850 p = 1) : d2812 p ≤ (0 : Int) + d190 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20379 p hg
    simpa only [d5850, d2812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20382 p hg
    simpa only [d5850, d2812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20963 (p : Pattern) (guard : d5850 p = 1) : d2812 p ≤ (0 : Int) + d3916 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2812, d3916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20379 p hg
    simpa only [d5850, d2812, d3916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2812, d3916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19737 p hg
    simpa only [d5850, d2812, d3916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20964 (p : Pattern) (guard : d5843 p = 1) : d315 p ≤ (0 : Int) + d315 p := by
  omega
theorem compare20965 (p : Pattern) (guard : d5850 p = 1) : d320 p ≤ (0 : Int) + d315 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20964 p hg
    simpa only [d5850, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19737 p hg
    simpa only [d5850, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20966 (p : Pattern) (guard : d5850 p = 1) : d2813 p ≤ (0 : Int) + d3917 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2813, d3917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20963 p hg
    simpa only [d2813, d3917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2813, d3917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20965 p hg
    simpa only [d2813, d3917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20967 (p : Pattern) (guard : d5850 p = 1) : d2814 p ≤ (0 : Int) + d3918 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2814, d3918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20962 p hg
    simpa only [d2814, d3918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2814, d3918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20966 p hg
    simpa only [d2814, d3918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20968 (p : Pattern) (guard : d5850 p = 1) : d2815 p ≤ (0 : Int) + d3919 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2815, d3919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20966 p hg
    simpa only [d2815, d3919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2815, d3919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2815, d3919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20969 (p : Pattern) (guard : d5850 p = 1) : d2816 p ≤ (0 : Int) + d3920 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2816, d3920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20967 p hg
    simpa only [d2816, d3920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2816, d3920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20968 p hg
    simpa only [d2816, d3920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20970 (p : Pattern) (guard : d5850 p = 1) : d2817 p ≤ (0 : Int) + d3921 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2817, d3921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20674 p hg
    simpa only [d2817, d3921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2817, d3921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20969 p hg
    simpa only [d2817, d3921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20971 (p : Pattern) (guard : d5850 p = 1) : d2818 p ≤ (0 : Int) + d3922 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2818, d3922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20970 p hg
    simpa only [d2818, d3922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2818, d3922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2818, d3922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20972 (p : Pattern) (guard : d5850 p = 1) : d2819 p ≤ (0 : Int) + d3923 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2819, d3923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20971 p hg
    simpa only [d2819, d3923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2819, d3923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2819, d3923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20973 (p : Pattern) (guard : d5850 p = 1) : d2820 p ≤ (0 : Int) + d3924 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2820, d3924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20961 p hg
    simpa only [d2820, d3924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2820, d3924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20972 p hg
    simpa only [d2820, d3924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20974 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3925 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20975 (p : Pattern) (guard : d5850 p = 1) : d2541 p ≤ (0 : Int) + d3926 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2541, d3926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20575 p hg
    simpa only [d5850, d2541, d3926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2541, d3926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20974 p hg
    simpa only [d5850, d2541, d3926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20976 (p : Pattern) (guard : d5850 p = 1) : d2542 p ≤ (0 : Int) + d3927 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2542, d3927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20573 p hg
    simpa only [d2542, d3927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2542, d3927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20975 p hg
    simpa only [d2542, d3927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20977 (p : Pattern) (guard : d5850 p = 1) : d2543 p ≤ (0 : Int) + d3928 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2543, d3928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20976 p hg
    simpa only [d2543, d3928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2543, d3928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2543, d3928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20978 (p : Pattern) (guard : d5850 p = 1) : d2611 p ≤ (0 : Int) + d3929 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2611, d3929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20647 p hg
    simpa only [d2611, d3929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2611, d3929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20977 p hg
    simpa only [d2611, d3929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20979 (p : Pattern) (guard : d5850 p = 1) : d2611 p ≤ (0 : Int) + d3930 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20978 p hg
    simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20682 p hg
    simpa only [d3930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20980 (p : Pattern) (guard : d5850 p = 1) : d2821 p ≤ (0 : Int) + d3931 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2821, d3931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20674 p hg
    simpa only [d2821, d3931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2821, d3931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20643 p hg
    simpa only [d2821, d3931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20981 (p : Pattern) (guard : d5850 p = 1) : d2822 p ≤ (0 : Int) + d3932 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2822, d3932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20979 p hg
    simpa only [d2822, d3932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2822, d3932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20980 p hg
    simpa only [d2822, d3932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20982 (p : Pattern) (guard : d5850 p = 1) : d2823 p ≤ (0 : Int) + d3933 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2823, d3933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20981 p hg
    simpa only [d2823, d3933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2823, d3933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20697 p hg
    simpa only [d2823, d3933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20983 (p : Pattern) (guard : d5850 p = 1) : d2824 p ≤ (0 : Int) + d3934 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2824, d3934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20969 p hg
    simpa only [d2824, d3934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2824, d3934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2824, d3934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20984 (p : Pattern) (guard : d5850 p = 1) : d2825 p ≤ (0 : Int) + d3935 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2825, d3935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20983 p hg
    simpa only [d2825, d3935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2825, d3935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2825, d3935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20985 (p : Pattern) (guard : d5850 p = 1) : d2826 p ≤ (0 : Int) + d3936 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2826, d3936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20984 p hg
    simpa only [d2826, d3936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2826, d3936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2826, d3936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20986 (p : Pattern) (guard : d5850 p = 1) : d2827 p ≤ (0 : Int) + d3937 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2827, d3937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20982 p hg
    simpa only [d2827, d3937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2827, d3937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20985 p hg
    simpa only [d2827, d3937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20987 (p : Pattern) (guard : d5850 p = 1) : d2828 p ≤ (0 : Int) + d3938 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2828, d3938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20973 p hg
    simpa only [d2828, d3938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2828, d3938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20986 p hg
    simpa only [d2828, d3938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20988 (p : Pattern) (guard : d5850 p = 1) : d2829 p ≤ (0 : Int) + d3939 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2829, d3939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20955 p hg
    simpa only [d2829, d3939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2829, d3939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20987 p hg
    simpa only [d2829, d3939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20989 (p : Pattern) (guard : d5850 p = 1) : d2830 p ≤ (0 : Int) + d3940 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2830, d3940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20987 p hg
    simpa only [d2830, d3940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2830, d3940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2830, d3940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20990 (p : Pattern) (guard : d5850 p = 1) : d2831 p ≤ (0 : Int) + d3941 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2831, d3941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20988 p hg
    simpa only [d2831, d3941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2831, d3941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20989 p hg
    simpa only [d2831, d3941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20991 (p : Pattern) (guard : d5850 p = 1) : d2832 p ≤ (0 : Int) + d3942 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2832, d3942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20740 p hg
    simpa only [d2832, d3942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2832, d3942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20990 p hg
    simpa only [d2832, d3942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20992 (p : Pattern) (guard : d5850 p = 1) : d2833 p ≤ (0 : Int) + d3943 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2833, d3943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20724 p hg
    simpa only [d2833, d3943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2833, d3943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20991 p hg
    simpa only [d2833, d3943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20993 (p : Pattern) (guard : d5850 p = 1) : d2834 p ≤ (0 : Int) + d3944 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2834, d3944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20782 p hg
    simpa only [d2834, d3944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2834, d3944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2834, d3944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20994 (p : Pattern) (guard : d5850 p = 1) : d2835 p ≤ (0 : Int) + d3945 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2835, d3945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20843 p hg
    simpa only [d2835, d3945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2835, d3945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20993 p hg
    simpa only [d2835, d3945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20995 (p : Pattern) (guard : d5850 p = 1) : d2836 p ≤ (0 : Int) + d3946 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2836, d3946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20993 p hg
    simpa only [d2836, d3946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2836, d3946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2836, d3946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20996 (p : Pattern) (guard : d5850 p = 1) : d2837 p ≤ (0 : Int) + d3947 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2837, d3947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20994 p hg
    simpa only [d2837, d3947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2837, d3947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20995 p hg
    simpa only [d2837, d3947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20997 (p : Pattern) (guard : d5850 p = 1) : d2838 p ≤ (0 : Int) + d3948 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2838, d3948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20819 p hg
    simpa only [d2838, d3948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2838, d3948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2838, d3948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20998 (p : Pattern) (guard : d5850 p = 1) : d2839 p ≤ (0 : Int) + d3949 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2839, d3949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20851 p hg
    simpa only [d2839, d3949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2839, d3949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20997 p hg
    simpa only [d2839, d3949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20999 (p : Pattern) (guard : d5850 p = 1) : d2840 p ≤ (0 : Int) + d3950 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2840, d3950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20997 p hg
    simpa only [d2840, d3950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2840, d3950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d2840, d3950, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
