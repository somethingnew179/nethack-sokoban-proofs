/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons126
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c17780 (pattern : Twelve) (guard : d1852 pattern = 1) : d1089 pattern ≤ (1 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1089, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17778 pattern childGuard
    simpa only [d1089, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1089, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17779 pattern childGuard
    simpa only [d1089, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17781 (pattern : Twelve) (guard : d1852 pattern = 1) : d1095 pattern ≤ (1 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17776 pattern childGuard
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17780 pattern childGuard
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17782 (pattern : Twelve) (guard : d1852 pattern = 1) : d1074 pattern ≤ (1 : Int) + d843 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1074, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11859 pattern childGuard
    simpa only [d1852, d1074, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1074, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17773 pattern childGuard
    simpa only [d1852, d1074, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17783 (pattern : Twelve) (guard : d1852 pattern = 1) : d1082 pattern ≤ (1 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1082, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11752 pattern childGuard
    simpa only [d1082, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1082, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17782 pattern childGuard
    simpa only [d1082, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17784 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d831 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17785 (pattern : Twelve) (guard : d1852 pattern = 1) : d1075 pattern ≤ (1 : Int) + d845 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1075, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11864 pattern childGuard
    simpa only [d1852, d1075, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1075, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17784 pattern childGuard
    simpa only [d1852, d1075, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17786 (pattern : Twelve) (guard : d1852 pattern = 1) : d1083 pattern ≤ (1 : Int) + d856 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1083, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11757 pattern childGuard
    simpa only [d1083, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1083, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17785 pattern childGuard
    simpa only [d1083, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17787 (pattern : Twelve) (guard : d1852 pattern = 1) : d1090 pattern ≤ (1 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1090, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17783 pattern childGuard
    simpa only [d1090, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1090, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17786 pattern childGuard
    simpa only [d1090, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17788 (pattern : Twelve) (guard : d1852 pattern = 1) : d1091 pattern ≤ (1 : Int) + d863 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1091, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17779 pattern childGuard
    simpa only [d1091, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1091, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17373 pattern childGuard
    simpa only [d1091, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17789 (pattern : Twelve) (guard : d1852 pattern = 1) : d1096 pattern ≤ (1 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1096, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17787 pattern childGuard
    simpa only [d1096, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1096, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17788 pattern childGuard
    simpa only [d1096, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17790 (pattern : Twelve) (guard : d1852 pattern = 1) : d1099 pattern ≤ (1 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1099, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17781 pattern childGuard
    simpa only [d1099, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1099, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17789 pattern childGuard
    simpa only [d1099, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17791 (pattern : Twelve) (guard : d1852 pattern = 1) : d1084 pattern ≤ (1 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1084, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11768 pattern childGuard
    simpa only [d1084, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1084, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17777 pattern childGuard
    simpa only [d1084, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17792 (pattern : Twelve) (guard : d1852 pattern = 1) : d1092 pattern ≤ (1 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1092, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17791 pattern childGuard
    simpa only [d1092, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1092, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17779 pattern childGuard
    simpa only [d1092, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17793 (pattern : Twelve) (guard : d1852 pattern = 1) : d1085 pattern ≤ (1 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1085, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11803 pattern childGuard
    simpa only [d1085, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1085, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17782 pattern childGuard
    simpa only [d1085, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17794 (pattern : Twelve) (guard : d1852 pattern = 1) : d1093 pattern ≤ (1 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1093, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17793 pattern childGuard
    simpa only [d1093, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1093, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17786 pattern childGuard
    simpa only [d1093, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17795 (pattern : Twelve) (guard : d1852 pattern = 1) : d1097 pattern ≤ (1 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1097, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17794 pattern childGuard
    simpa only [d1097, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1097, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17788 pattern childGuard
    simpa only [d1097, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17796 (pattern : Twelve) (guard : d1852 pattern = 1) : d1100 pattern ≤ (1 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1100, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17792 pattern childGuard
    simpa only [d1100, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1100, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17795 pattern childGuard
    simpa only [d1100, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17797 (pattern : Twelve) (guard : d1852 pattern = 1) : d1102 pattern ≤ (1 : Int) + d869 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17790 pattern childGuard
    simpa only [d1102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17796 pattern childGuard
    simpa only [d1102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17798 (pattern : Twelve) (guard : d1852 pattern = 1) : d1103 pattern ≤ (1 : Int) + d869 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17797 pattern childGuard
    simpa only [d1103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17796 pattern childGuard
    simpa only [d1103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17799 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d882 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17800 (pattern : Twelve) (guard : d1852 pattern = 1) : d438 pattern ≤ (1 : Int) + d890 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d438, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1852, d438, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d438, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17799 pattern childGuard
    simpa only [d1852, d438, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17801 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d883 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17802 (pattern : Twelve) (guard : d1852 pattern = 1) : d1073 pattern ≤ (1 : Int) + d891 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1073, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d1852, d1073, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1073, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17801 pattern childGuard
    simpa only [d1852, d1073, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17803 (pattern : Twelve) (guard : d1852 pattern = 1) : d1084 pattern ≤ (1 : Int) + d898 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1084, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17800 pattern childGuard
    simpa only [d1084, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1084, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17802 pattern childGuard
    simpa only [d1084, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17804 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d884 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17805 (pattern : Twelve) (guard : d1852 pattern = 1) : d432 pattern ≤ (1 : Int) + d892 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d432, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11744 pattern childGuard
    simpa only [d1852, d432, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d432, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17804 pattern childGuard
    simpa only [d1852, d432, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17806 (pattern : Twelve) (guard : d1852 pattern = 1) : d1072 pattern ≤ (1 : Int) + d893 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1072, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11845 pattern childGuard
    simpa only [d1852, d1072, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1072, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17801 pattern childGuard
    simpa only [d1852, d1072, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17807 (pattern : Twelve) (guard : d1852 pattern = 1) : d1081 pattern ≤ (1 : Int) + d899 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1081, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17805 pattern childGuard
    simpa only [d1081, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1081, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17806 pattern childGuard
    simpa only [d1081, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17808 (pattern : Twelve) (guard : d1852 pattern = 1) : d1092 pattern ≤ (1 : Int) + d902 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1092, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17803 pattern childGuard
    simpa only [d1092, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1092, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17807 pattern childGuard
    simpa only [d1092, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17809 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d885 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17810 (pattern : Twelve) (guard : d1852 pattern = 1) : d441 pattern ≤ (1 : Int) + d894 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d441, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11732 pattern childGuard
    simpa only [d1852, d441, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d441, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17809 pattern childGuard
    simpa only [d1852, d441, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17811 (pattern : Twelve) (guard : d1 pattern = 1) : d886 pattern ≤ (1 : Int) + d886 pattern := by
  omega
theorem c17812 (pattern : Twelve) (guard : d1852 pattern = 1) : d1076 pattern ≤ (1 : Int) + d895 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1076, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17811 pattern childGuard
    simpa only [d1852, d1076, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1076, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17801 pattern childGuard
    simpa only [d1852, d1076, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17813 (pattern : Twelve) (guard : d1852 pattern = 1) : d1086 pattern ≤ (1 : Int) + d900 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1086, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17810 pattern childGuard
    simpa only [d1086, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1086, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17812 pattern childGuard
    simpa only [d1086, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17814 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d887 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17815 (pattern : Twelve) (guard : d1852 pattern = 1) : d436 pattern ≤ (1 : Int) + d896 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d436, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11755 pattern childGuard
    simpa only [d1852, d436, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d436, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17814 pattern childGuard
    simpa only [d1852, d436, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17816 (pattern : Twelve) (guard : d1 pattern = 1) : d888 pattern ≤ (1 : Int) + d888 pattern := by
  omega
theorem c17817 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d889 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17818 (pattern : Twelve) (guard : d1852 pattern = 1) : d1077 pattern ≤ (1 : Int) + d897 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1077, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17816 pattern childGuard
    simpa only [d1852, d1077, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1077, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17817 pattern childGuard
    simpa only [d1852, d1077, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17819 (pattern : Twelve) (guard : d1852 pattern = 1) : d1087 pattern ≤ (1 : Int) + d901 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1087, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17815 pattern childGuard
    simpa only [d1087, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1087, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17818 pattern childGuard
    simpa only [d1087, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17820 (pattern : Twelve) (guard : d1852 pattern = 1) : d1094 pattern ≤ (1 : Int) + d903 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1094, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17813 pattern childGuard
    simpa only [d1094, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1094, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17819 pattern childGuard
    simpa only [d1094, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17821 (pattern : Twelve) (guard : d1852 pattern = 1) : d1091 pattern ≤ (1 : Int) + d904 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1091, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17807 pattern childGuard
    simpa only [d1091, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1091, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17373 pattern childGuard
    simpa only [d1091, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17822 (pattern : Twelve) (guard : d1852 pattern = 1) : d1098 pattern ≤ (1 : Int) + d905 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1098, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17820 pattern childGuard
    simpa only [d1098, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1098, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17821 pattern childGuard
    simpa only [d1098, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17823 (pattern : Twelve) (guard : d1852 pattern = 1) : d1101 pattern ≤ (1 : Int) + d906 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1101, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17808 pattern childGuard
    simpa only [d1101, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1101, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17822 pattern childGuard
    simpa only [d1101, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17824 (pattern : Twelve) (guard : d1852 pattern = 1) : d1104 pattern ≤ (1 : Int) + d907 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1104, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17798 pattern childGuard
    simpa only [d1104, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1104, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17823 pattern childGuard
    simpa only [d1104, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17825 (pattern : Twelve) (guard : d1852 pattern = 1) : d1294 pattern ≤ (1 : Int) + d1294 pattern := by
  omega
theorem c17826 (pattern : Twelve) (guard : d1852 pattern = 1) : d1472 pattern ≤ (1 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1472, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11842 pattern childGuard
    simpa only [d1472, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1472, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17825 pattern childGuard
    simpa only [d1472, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17827 (pattern : Twelve) (guard : d1852 pattern = 1) : d1296 pattern ≤ (1 : Int) + d1296 pattern := by
  omega
theorem c17828 (pattern : Twelve) (guard : d1852 pattern = 1) : d1473 pattern ≤ (1 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1473, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11847 pattern childGuard
    simpa only [d1473, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1473, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17827 pattern childGuard
    simpa only [d1473, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17829 (pattern : Twelve) (guard : d1852 pattern = 1) : d1479 pattern ≤ (1 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1479, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17826 pattern childGuard
    simpa only [d1479, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1479, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17828 pattern childGuard
    simpa only [d1479, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17830 (pattern : Twelve) (guard : d1852 pattern = 1) : d1474 pattern ≤ (1 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1474, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11852 pattern childGuard
    simpa only [d1474, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1474, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17825 pattern childGuard
    simpa only [d1474, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17831 (pattern : Twelve) (guard : d1852 pattern = 1) : d1480 pattern ≤ (1 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1480, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17830 pattern childGuard
    simpa only [d1480, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1480, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17828 pattern childGuard
    simpa only [d1480, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17832 (pattern : Twelve) (guard : d1852 pattern = 1) : d1484 pattern ≤ (1 : Int) + d1313 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17829 pattern childGuard
    simpa only [d1484, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17831 pattern childGuard
    simpa only [d1484, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17833 (pattern : Twelve) (guard : d1852 pattern = 1) : d1298 pattern ≤ (1 : Int) + d1298 pattern := by
  omega
theorem c17834 (pattern : Twelve) (guard : d1852 pattern = 1) : d1475 pattern ≤ (1 : Int) + d1307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1475, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11861 pattern childGuard
    simpa only [d1475, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1475, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17833 pattern childGuard
    simpa only [d1475, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17835 (pattern : Twelve) (guard : d1852 pattern = 1) : d1300 pattern ≤ (1 : Int) + d1300 pattern := by
  omega
theorem c17836 (pattern : Twelve) (guard : d1852 pattern = 1) : d1476 pattern ≤ (1 : Int) + d1308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1476, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11866 pattern childGuard
    simpa only [d1476, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1476, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17835 pattern childGuard
    simpa only [d1476, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17837 (pattern : Twelve) (guard : d1852 pattern = 1) : d1481 pattern ≤ (1 : Int) + d1314 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1481, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17834 pattern childGuard
    simpa only [d1481, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1481, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17836 pattern childGuard
    simpa only [d1481, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17838 (pattern : Twelve) (guard : d1852 pattern = 1) : d1482 pattern ≤ (1 : Int) + d1315 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1482, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17828 pattern childGuard
    simpa only [d1482, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1482, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17373 pattern childGuard
    simpa only [d1482, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17839 (pattern : Twelve) (guard : d1852 pattern = 1) : d1485 pattern ≤ (1 : Int) + d1319 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1485, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17837 pattern childGuard
    simpa only [d1485, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1485, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17838 pattern childGuard
    simpa only [d1485, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17840 (pattern : Twelve) (guard : d1852 pattern = 1) : d1487 pattern ≤ (1 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1487, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17832 pattern childGuard
    simpa only [d1487, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1487, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17839 pattern childGuard
    simpa only [d1487, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17841 (pattern : Twelve) (guard : d1852 pattern = 1) : d1488 pattern ≤ (1 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1488, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17831 pattern childGuard
    simpa only [d1488, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1488, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17839 pattern childGuard
    simpa only [d1488, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17842 (pattern : Twelve) (guard : d1852 pattern = 1) : d1490 pattern ≤ (1 : Int) + d1321 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17840 pattern childGuard
    simpa only [d1490, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17841 pattern childGuard
    simpa only [d1490, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17843 (pattern : Twelve) (guard : d1852 pattern = 1) : d1491 pattern ≤ (1 : Int) + d1321 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17842 pattern childGuard
    simpa only [d1491, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17841 pattern childGuard
    simpa only [d1491, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17844 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d1333 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17845 (pattern : Twelve) (guard : d1852 pattern = 1) : d1073 pattern ≤ (1 : Int) + d1339 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1073, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11054 pattern childGuard
    simpa only [d1852, d1073, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1073, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17844 pattern childGuard
    simpa only [d1852, d1073, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17846 (pattern : Twelve) (guard : d1852 pattern = 1) : d1474 pattern ≤ (1 : Int) + d1345 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1474, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17845 pattern childGuard
    simpa only [d1474, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1474, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17825 pattern childGuard
    simpa only [d1474, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17847 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d1334 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17848 (pattern : Twelve) (guard : d1852 pattern = 1) : d1072 pattern ≤ (1 : Int) + d1340 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1072, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11845 pattern childGuard
    simpa only [d1852, d1072, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1072, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17847 pattern childGuard
    simpa only [d1852, d1072, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17849 (pattern : Twelve) (guard : d1852 pattern = 1) : d1473 pattern ≤ (1 : Int) + d1346 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1473, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17848 pattern childGuard
    simpa only [d1473, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1473, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17827 pattern childGuard
    simpa only [d1473, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17850 (pattern : Twelve) (guard : d1852 pattern = 1) : d1480 pattern ≤ (1 : Int) + d1349 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1480, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17846 pattern childGuard
    simpa only [d1480, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1480, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17849 pattern childGuard
    simpa only [d1480, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17851 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d1335 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17852 (pattern : Twelve) (guard : d1852 pattern = 1) : d1074 pattern ≤ (1 : Int) + d1341 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1074, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11859 pattern childGuard
    simpa only [d1852, d1074, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1074, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17851 pattern childGuard
    simpa only [d1852, d1074, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17853 (pattern : Twelve) (guard : d1852 pattern = 1) : d1342 pattern ≤ (1 : Int) + d1342 pattern := by
  omega
theorem c17854 (pattern : Twelve) (guard : d1852 pattern = 1) : d1477 pattern ≤ (1 : Int) + d1347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1477, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17852 pattern childGuard
    simpa only [d1477, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1477, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17853 pattern childGuard
    simpa only [d1477, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17855 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d1337 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17856 (pattern : Twelve) (guard : d1852 pattern = 1) : d1075 pattern ≤ (1 : Int) + d1343 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1075, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11864 pattern childGuard
    simpa only [d1852, d1075, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1075, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17855 pattern childGuard
    simpa only [d1852, d1075, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17857 (pattern : Twelve) (guard : d1852 pattern = 1) : d1344 pattern ≤ (1 : Int) + d1344 pattern := by
  omega
theorem c17858 (pattern : Twelve) (guard : d1852 pattern = 1) : d1478 pattern ≤ (1 : Int) + d1348 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1478, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17856 pattern childGuard
    simpa only [d1478, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1478, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17857 pattern childGuard
    simpa only [d1478, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17859 (pattern : Twelve) (guard : d1852 pattern = 1) : d1483 pattern ≤ (1 : Int) + d1350 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1483, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17854 pattern childGuard
    simpa only [d1483, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1483, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17858 pattern childGuard
    simpa only [d1483, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17860 (pattern : Twelve) (guard : d1852 pattern = 1) : d1482 pattern ≤ (1 : Int) + d1351 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1482, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17849 pattern childGuard
    simpa only [d1482, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1482, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17373 pattern childGuard
    simpa only [d1482, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17861 (pattern : Twelve) (guard : d1852 pattern = 1) : d1486 pattern ≤ (1 : Int) + d1352 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1486, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17859 pattern childGuard
    simpa only [d1486, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1486, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17860 pattern childGuard
    simpa only [d1486, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17862 (pattern : Twelve) (guard : d1852 pattern = 1) : d1489 pattern ≤ (1 : Int) + d1353 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1489, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17850 pattern childGuard
    simpa only [d1489, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1489, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17861 pattern childGuard
    simpa only [d1489, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17863 (pattern : Twelve) (guard : d1852 pattern = 1) : d1492 pattern ≤ (1 : Int) + d1354 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1492, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17843 pattern childGuard
    simpa only [d1492, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1492, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17862 pattern childGuard
    simpa only [d1492, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17864 (pattern : Twelve) (guard : d1852 pattern = 1) : d1650 pattern ≤ (1 : Int) + d1650 pattern := by
  omega
theorem c17865 (pattern : Twelve) (guard : d1852 pattern = 1) : d1730 pattern ≤ (1 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1730, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11898 pattern childGuard
    simpa only [d1730, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1730, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17864 pattern childGuard
    simpa only [d1730, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17866 (pattern : Twelve) (guard : d1852 pattern = 1) : d1731 pattern ≤ (1 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1731, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11903 pattern childGuard
    simpa only [d1731, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1731, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17835 pattern childGuard
    simpa only [d1731, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17867 (pattern : Twelve) (guard : d1852 pattern = 1) : d1736 pattern ≤ (1 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1736, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17865 pattern childGuard
    simpa only [d1736, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1736, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17866 pattern childGuard
    simpa only [d1736, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17868 (pattern : Twelve) (guard : d1852 pattern = 1) : d1653 pattern ≤ (1 : Int) + d1653 pattern := by
  omega
theorem c17869 (pattern : Twelve) (guard : d1852 pattern = 1) : d1732 pattern ≤ (1 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1732, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11913 pattern childGuard
    simpa only [d1732, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1732, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17868 pattern childGuard
    simpa only [d1732, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17870 (pattern : Twelve) (guard : d1852 pattern = 1) : d1655 pattern ≤ (1 : Int) + d1655 pattern := by
  omega
theorem c17871 (pattern : Twelve) (guard : d1852 pattern = 1) : d1733 pattern ≤ (1 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1733, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11918 pattern childGuard
    simpa only [d1733, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1733, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17870 pattern childGuard
    simpa only [d1733, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17872 (pattern : Twelve) (guard : d1852 pattern = 1) : d1737 pattern ≤ (1 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1737, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17869 pattern childGuard
    simpa only [d1737, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1737, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17871 pattern childGuard
    simpa only [d1737, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17873 (pattern : Twelve) (guard : d1852 pattern = 1) : d1738 pattern ≤ (1 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1738, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17866 pattern childGuard
    simpa only [d1738, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1738, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17373 pattern childGuard
    simpa only [d1738, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17874 (pattern : Twelve) (guard : d1852 pattern = 1) : d1740 pattern ≤ (1 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1740, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17872 pattern childGuard
    simpa only [d1740, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1740, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17873 pattern childGuard
    simpa only [d1740, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17875 (pattern : Twelve) (guard : d1852 pattern = 1) : d1742 pattern ≤ (1 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1742, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17867 pattern childGuard
    simpa only [d1742, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1742, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17874 pattern childGuard
    simpa only [d1742, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17876 (pattern : Twelve) (guard : d1852 pattern = 1) : d1294 pattern ≤ (1 : Int) + d1668 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1294, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11067 pattern childGuard
    simpa only [d1852, d1294, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1294, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11912 pattern childGuard
    simpa only [d1852, d1294, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17877 (pattern : Twelve) (guard : d1852 pattern = 1) : d1730 pattern ≤ (1 : Int) + d1671 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1730, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17876 pattern childGuard
    simpa only [d1730, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1730, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17864 pattern childGuard
    simpa only [d1730, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17878 (pattern : Twelve) (guard : d1852 pattern = 1) : d1736 pattern ≤ (1 : Int) + d1674 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1736, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17877 pattern childGuard
    simpa only [d1736, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1736, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17866 pattern childGuard
    simpa only [d1736, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17879 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d1666 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17880 (pattern : Twelve) (guard : d1852 pattern = 1) : d1298 pattern ≤ (1 : Int) + d1669 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1298, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11911 pattern childGuard
    simpa only [d1852, d1298, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1298, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17879 pattern childGuard
    simpa only [d1852, d1298, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17881 (pattern : Twelve) (guard : d1852 pattern = 1) : d1734 pattern ≤ (1 : Int) + d1672 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1734, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17880 pattern childGuard
    simpa only [d1734, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1734, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17835 pattern childGuard
    simpa only [d1734, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17882 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (1 : Int) + d1667 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c17883 (pattern : Twelve) (guard : d1852 pattern = 1) : d1300 pattern ≤ (1 : Int) + d1670 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1300, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11916 pattern childGuard
    simpa only [d1852, d1300, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1300, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17882 pattern childGuard
    simpa only [d1852, d1300, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17884 (pattern : Twelve) (guard : d1852 pattern = 1) : d1626 pattern ≤ (1 : Int) + d1626 pattern := by
  omega
theorem c17885 (pattern : Twelve) (guard : d1852 pattern = 1) : d1735 pattern ≤ (1 : Int) + d1673 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1735, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17883 pattern childGuard
    simpa only [d1735, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1735, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17884 pattern childGuard
    simpa only [d1735, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17886 (pattern : Twelve) (guard : d1852 pattern = 1) : d1739 pattern ≤ (1 : Int) + d1675 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1739, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17881 pattern childGuard
    simpa only [d1739, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1739, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17885 pattern childGuard
    simpa only [d1739, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17887 (pattern : Twelve) (guard : d1852 pattern = 1) : d1741 pattern ≤ (1 : Int) + d1676 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1741, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17886 pattern childGuard
    simpa only [d1741, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1741, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17873 pattern childGuard
    simpa only [d1741, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17888 (pattern : Twelve) (guard : d1852 pattern = 1) : d1743 pattern ≤ (1 : Int) + d1677 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1743, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17878 pattern childGuard
    simpa only [d1743, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1743, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17887 pattern childGuard
    simpa only [d1743, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17889 (pattern : Twelve) (guard : d1852 pattern = 1) : d1744 pattern ≤ (1 : Int) + d1678 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1744, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17875 pattern childGuard
    simpa only [d1744, d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1744, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17888 pattern childGuard
    simpa only [d1744, d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17890 (pattern : Twelve) (guard : d1865 pattern = 1) : d171 pattern ≤ (1 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12208 pattern childGuard
    simpa only [d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12219 pattern childGuard
    simpa only [d171, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17891 (pattern : Twelve) (guard : d1865 pattern = 1) : d500 pattern ≤ (1 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d500, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12231 pattern childGuard
    simpa only [d500, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d500, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12223 pattern childGuard
    simpa only [d500, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17892 (pattern : Twelve) (guard : d1865 pattern = 1) : d533 pattern ≤ (1 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d533, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17890 pattern childGuard
    simpa only [d533, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d533, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17891 pattern childGuard
    simpa only [d533, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17893 (pattern : Twelve) (guard : d1865 pattern = 1) : d561 pattern ≤ (1 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d561, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12215 pattern childGuard
    simpa only [d561, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d561, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17892 pattern childGuard
    simpa only [d561, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17894 (pattern : Twelve) (guard : d1865 pattern = 1) : d162 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11049 pattern childGuard
    simpa only [d1865, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15948 pattern childGuard
    simpa only [d1865, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17895 (pattern : Twelve) (guard : d1865 pattern = 1) : d501 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17894 pattern childGuard
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12281 pattern childGuard
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17896 (pattern : Twelve) (guard : d1865 pattern = 1) : d534 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12214 pattern childGuard
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17895 pattern childGuard
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17897 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (1 : Int) + d8 pattern := by
  omega
theorem c17898 (pattern : Twelve) (guard : d1865 pattern = 1) : d481 pattern ≤ (1 : Int) + d18 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d481, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17897 pattern childGuard
    simpa only [d1865, d481, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d481, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12259 pattern childGuard
    simpa only [d1865, d481, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17899 (pattern : Twelve) (guard : d1865 pattern = 1) : d502 pattern ≤ (1 : Int) + d28 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d502, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12231 pattern childGuard
    simpa only [d502, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d502, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17898 pattern childGuard
    simpa only [d502, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17900 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (1 : Int) + d10 pattern := by
  omega
theorem c17901 (pattern : Twelve) (guard : d1865 pattern = 1) : d482 pattern ≤ (1 : Int) + d19 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d482, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17900 pattern childGuard
    simpa only [d1865, d482, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d482, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12270 pattern childGuard
    simpa only [d1865, d482, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17902 (pattern : Twelve) (guard : d1865 pattern = 1) : d503 pattern ≤ (1 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d503, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17901 pattern childGuard
    simpa only [d503, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d503, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d503, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17903 (pattern : Twelve) (guard : d1865 pattern = 1) : d535 pattern ≤ (1 : Int) + d51 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d535, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17899 pattern childGuard
    simpa only [d535, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d535, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17902 pattern childGuard
    simpa only [d535, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17904 (pattern : Twelve) (guard : d1865 pattern = 1) : d562 pattern ≤ (1 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d562, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17896 pattern childGuard
    simpa only [d562, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d562, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17903 pattern childGuard
    simpa only [d562, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17905 (pattern : Twelve) (guard : d1865 pattern = 1) : d588 pattern ≤ (1 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d588, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17893 pattern childGuard
    simpa only [d588, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d588, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17904 pattern childGuard
    simpa only [d588, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17906 (pattern : Twelve) (guard : d1 pattern = 1) : d12 pattern ≤ (1 : Int) + d12 pattern := by
  omega
theorem c17907 (pattern : Twelve) (guard : d1865 pattern = 1) : d486 pattern ≤ (1 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d486, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17906 pattern childGuard
    simpa only [d1865, d486, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d486, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12536 pattern childGuard
    simpa only [d1865, d486, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17908 (pattern : Twelve) (guard : d1865 pattern = 1) : d505 pattern ≤ (1 : Int) + d31 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d505, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12253 pattern childGuard
    simpa only [d505, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d505, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17907 pattern childGuard
    simpa only [d505, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17909 (pattern : Twelve) (guard : d1865 pattern = 1) : d536 pattern ≤ (1 : Int) + d52 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d536, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12251 pattern childGuard
    simpa only [d536, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d536, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17908 pattern childGuard
    simpa only [d536, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17910 (pattern : Twelve) (guard : d1865 pattern = 1) : d506 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d506, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12253 pattern childGuard
    simpa only [d506, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d506, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12294 pattern childGuard
    simpa only [d506, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17911 (pattern : Twelve) (guard : d1 pattern = 1) : d13 pattern ≤ (1 : Int) + d13 pattern := by
  omega
theorem c17912 (pattern : Twelve) (guard : d1865 pattern = 1) : d170 pattern ≤ (1 : Int) + d21 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d170, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17911 pattern childGuard
    simpa only [d1865, d170, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d170, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12342 pattern childGuard
    simpa only [d1865, d170, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17913 (pattern : Twelve) (guard : d1865 pattern = 1) : d507 pattern ≤ (1 : Int) + d32 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d507, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d507, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d507, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17912 pattern childGuard
    simpa only [d507, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17914 (pattern : Twelve) (guard : d1865 pattern = 1) : d537 pattern ≤ (1 : Int) + d53 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d537, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17910 pattern childGuard
    simpa only [d537, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d537, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17913 pattern childGuard
    simpa only [d537, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17915 (pattern : Twelve) (guard : d1865 pattern = 1) : d563 pattern ≤ (1 : Int) + d74 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d563, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17909 pattern childGuard
    simpa only [d563, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d563, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17914 pattern childGuard
    simpa only [d563, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17916 (pattern : Twelve) (guard : d1865 pattern = 1) : d22 pattern ≤ (1 : Int) + d22 pattern := by
  omega
theorem c17917 (pattern : Twelve) (guard : d1865 pattern = 1) : d508 pattern ≤ (1 : Int) + d33 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d508, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12281 pattern childGuard
    simpa only [d508, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d508, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17916 pattern childGuard
    simpa only [d508, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17918 (pattern : Twelve) (guard : d1865 pattern = 1) : d538 pattern ≤ (1 : Int) + d54 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d538, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17910 pattern childGuard
    simpa only [d538, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d538, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17917 pattern childGuard
    simpa only [d538, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17919 (pattern : Twelve) (guard : d1865 pattern = 1) : d539 pattern ≤ (1 : Int) + d55 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d539, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12298 pattern childGuard
    simpa only [d539, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d539, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17902 pattern childGuard
    simpa only [d539, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
