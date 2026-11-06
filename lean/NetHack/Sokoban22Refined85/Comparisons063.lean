/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons062
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare8820 (p : Pattern) (guard : d4670 p = 1) : d1084 p ≤ (0 : Int) + d885 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1084, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8817 p hg
    simpa only [d1084, d885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1084, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8819 p hg
    simpa only [d1084, d885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8821 (p : Pattern) (guard : d0 p = 1) : d371 p ≤ (0 : Int) + d134 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8822 (p : Pattern) (guard : d4395 p = 1) : d1085 p ≤ (0 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1085, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d1085, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1085, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8821 p hg
    simpa only [d4395, d1085, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8823 (p : Pattern) (guard : d0 p = 1) : d1051 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8824 (p : Pattern) (guard : d4670 p = 1) : d1086 p ≤ (0 : Int) + d886 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1086, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8822 p hg
    simpa only [d4670, d1086, d886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1086, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8823 p hg
    simpa only [d4670, d1086, d886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8825 (p : Pattern) (guard : d4670 p = 1) : d1087 p ≤ (0 : Int) + d887 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1087, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8824 p hg
    simpa only [d1087, d887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1087, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8787 p hg
    simpa only [d1087, d887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8826 (p : Pattern) (guard : d4670 p = 1) : d1088 p ≤ (0 : Int) + d888 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1088, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8820 p hg
    simpa only [d1088, d888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1088, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8825 p hg
    simpa only [d1088, d888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8827 (p : Pattern) (guard : d0 p = 1) : d1059 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8828 (p : Pattern) (guard : d4670 p = 1) : d1090 p ≤ (0 : Int) + d889 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1090, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7974 p hg
    simpa only [d4670, d1090, d889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1090, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8827 p hg
    simpa only [d4670, d1090, d889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8829 (p : Pattern) (guard : d4670 p = 1) : d1091 p ≤ (0 : Int) + d890 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1091, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8828 p hg
    simpa only [d1091, d890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1091, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8794 p hg
    simpa only [d1091, d890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8830 (p : Pattern) (guard : d4670 p = 1) : d1092 p ≤ (0 : Int) + d891 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1092, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8829 p hg
    simpa only [d1092, d891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1092, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8803 p hg
    simpa only [d1092, d891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8831 (p : Pattern) (guard : d4670 p = 1) : d1093 p ≤ (0 : Int) + d892 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1093, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8826 p hg
    simpa only [d1093, d892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1093, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8830 p hg
    simpa only [d1093, d892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8832 (p : Pattern) (guard : d4670 p = 1) : d1094 p ≤ (0 : Int) + d893 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1094, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8830 p hg
    simpa only [d1094, d893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1094, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6484 p hg
    simpa only [d1094, d893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8833 (p : Pattern) (guard : d4670 p = 1) : d1095 p ≤ (0 : Int) + d894 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1095, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8831 p hg
    simpa only [d1095, d894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1095, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8832 p hg
    simpa only [d1095, d894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8834 (p : Pattern) (guard : d4670 p = 1) : d1096 p ≤ (0 : Int) + d895 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1096, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8815 p hg
    simpa only [d1096, d895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1096, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8833 p hg
    simpa only [d1096, d895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8835 (p : Pattern) (guard : d4670 p = 1) : d1097 p ≤ (0 : Int) + d896 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1097, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8741 p hg
    simpa only [d1097, d896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1097, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8834 p hg
    simpa only [d1097, d896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8836 (p : Pattern) (guard : d4670 p = 1) : d1098 p ≤ (0 : Int) + d897 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1098, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8772 p hg
    simpa only [d1098, d897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1098, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8835 p hg
    simpa only [d1098, d897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8837 (p : Pattern) (guard : d4395 p = 1) : d1001 p ≤ (0 : Int) + d188 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1001, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4395, d1001, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1001, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8687 p hg
    simpa only [d4395, d1001, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8838 (p : Pattern) (guard : d4670 p = 1) : d1002 p ≤ (0 : Int) + d898 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1002, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8837 p hg
    simpa only [d4670, d1002, d898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1002, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8727 p hg
    simpa only [d4670, d1002, d898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8839 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d194 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8840 (p : Pattern) (guard : d4395 p = 1) : d968 p ≤ (0 : Int) + d899 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d968, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4395, d968, d899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d968, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8839 p hg
    simpa only [d4395, d968, d899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8841 (p : Pattern) (guard : d4670 p = 1) : d969 p ≤ (0 : Int) + d900 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d969, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8840 p hg
    simpa only [d4670, d969, d900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d969, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4670, d969, d900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8842 (p : Pattern) (guard : d4670 p = 1) : d1003 p ≤ (0 : Int) + d901 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1003, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8838 p hg
    simpa only [d1003, d901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1003, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8841 p hg
    simpa only [d1003, d901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8843 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d198 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8844 (p : Pattern) (guard : d4395 p = 1) : d968 p ≤ (0 : Int) + d199 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d968, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4395, d968, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d968, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8843 p hg
    simpa only [d4395, d968, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8845 (p : Pattern) (guard : d4670 p = 1) : d1099 p ≤ (0 : Int) + d902 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1099, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8844 p hg
    simpa only [d4670, d1099, d902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1099, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8693 p hg
    simpa only [d4670, d1099, d902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8846 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d83 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8847 (p : Pattern) (guard : d4395 p = 1) : d1100 p ≤ (0 : Int) + d903 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1100, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare847 p hg
    simpa only [d4395, d1100, d903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1100, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8846 p hg
    simpa only [d4395, d1100, d903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8848 (p : Pattern) (guard : d4670 p = 1) : d1101 p ≤ (0 : Int) + d904 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1101, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8847 p hg
    simpa only [d4670, d1101, d904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1101, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4670, d1101, d904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8849 (p : Pattern) (guard : d4670 p = 1) : d1102 p ≤ (0 : Int) + d905 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1102, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8845 p hg
    simpa only [d1102, d905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1102, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8848 p hg
    simpa only [d1102, d905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8850 (p : Pattern) (guard : d4670 p = 1) : d1103 p ≤ (0 : Int) + d906 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1103, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8842 p hg
    simpa only [d1103, d906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1103, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8849 p hg
    simpa only [d1103, d906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8851 (p : Pattern) (guard : d4670 p = 1) : d1104 p ≤ (0 : Int) + d907 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1104, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8767 p hg
    simpa only [d1104, d907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1104, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8850 p hg
    simpa only [d1104, d907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8852 (p : Pattern) (guard : d4670 p = 1) : d1105 p ≤ (0 : Int) + d908 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1105, d908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8850 p hg
    simpa only [d1105, d908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1105, d908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6484 p hg
    simpa only [d1105, d908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8853 (p : Pattern) (guard : d4670 p = 1) : d1106 p ≤ (0 : Int) + d909 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1106, d909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8851 p hg
    simpa only [d1106, d909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1106, d909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8852 p hg
    simpa only [d1106, d909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8854 (p : Pattern) (guard : d4670 p = 1) : d1107 p ≤ (0 : Int) + d910 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1107, d910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8760 p hg
    simpa only [d1107, d910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1107, d910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8853 p hg
    simpa only [d1107, d910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8855 (p : Pattern) (guard : d4670 p = 1) : d1108 p ≤ (0 : Int) + d911 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1108, d911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8741 p hg
    simpa only [d1108, d911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1108, d911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8854 p hg
    simpa only [d1108, d911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8856 (p : Pattern) (guard : d0 p = 1) : d448 p ≤ (0 : Int) + d211 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8857 (p : Pattern) (guard : d4395 p = 1) : d1109 p ≤ (0 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1109, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d1109, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1109, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8856 p hg
    simpa only [d4395, d1109, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8858 (p : Pattern) (guard : d0 p = 1) : d1051 p ≤ (0 : Int) + d451 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8859 (p : Pattern) (guard : d4670 p = 1) : d1110 p ≤ (0 : Int) + d912 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1110, d912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8857 p hg
    simpa only [d4670, d1110, d912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1110, d912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8858 p hg
    simpa only [d4670, d1110, d912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8860 (p : Pattern) (guard : d4670 p = 1) : d1111 p ≤ (0 : Int) + d913 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1111, d913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8859 p hg
    simpa only [d1111, d913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1111, d913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8787 p hg
    simpa only [d1111, d913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8861 (p : Pattern) (guard : d4670 p = 1) : d1112 p ≤ (0 : Int) + d914 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1112, d914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8779 p hg
    simpa only [d1112, d914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1112, d914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8860 p hg
    simpa only [d1112, d914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8862 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d211 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8863 (p : Pattern) (guard : d4395 p = 1) : d1059 p ≤ (0 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1059, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d1059, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1059, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8862 p hg
    simpa only [d4395, d1059, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8864 (p : Pattern) (guard : d4670 p = 1) : d1065 p ≤ (0 : Int) + d915 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1065, d915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8863 p hg
    simpa only [d4670, d1065, d915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1065, d915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8798 p hg
    simpa only [d4670, d1065, d915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8865 (p : Pattern) (guard : d4670 p = 1) : d1067 p ≤ (0 : Int) + d916 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1067, d916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8864 p hg
    simpa only [d1067, d916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1067, d916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8802 p hg
    simpa only [d1067, d916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8866 (p : Pattern) (guard : d4670 p = 1) : d1068 p ≤ (0 : Int) + d917 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1068, d917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8795 p hg
    simpa only [d1068, d917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1068, d917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8865 p hg
    simpa only [d1068, d917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8867 (p : Pattern) (guard : d4670 p = 1) : d1113 p ≤ (0 : Int) + d918 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1113, d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8861 p hg
    simpa only [d1113, d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1113, d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8866 p hg
    simpa only [d1113, d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8868 (p : Pattern) (guard : d4670 p = 1) : d1114 p ≤ (0 : Int) + d919 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1114, d919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8808 p hg
    simpa only [d1114, d919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1114, d919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8865 p hg
    simpa only [d1114, d919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8869 (p : Pattern) (guard : d4670 p = 1) : d1115 p ≤ (0 : Int) + d920 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1115, d920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8868 p hg
    simpa only [d1115, d920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1115, d920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6568 p hg
    simpa only [d1115, d920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8870 (p : Pattern) (guard : d4670 p = 1) : d1116 p ≤ (0 : Int) + d921 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1116, d921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8867 p hg
    simpa only [d1116, d921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1116, d921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8869 p hg
    simpa only [d1116, d921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8871 (p : Pattern) (guard : d0 p = 1) : d1118 p ≤ (0 : Int) + d403 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8872 (p : Pattern) (guard : d4670 p = 1) : d1119 p ≤ (0 : Int) + d884 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1119, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d4670, d1119, d884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1119, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8871 p hg
    simpa only [d4670, d1119, d884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8873 (p : Pattern) (guard : d4395 p = 1) : d1120 p ≤ (0 : Int) + d922 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1120, d922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2440 p hg
    simpa only [d4395, d1120, d922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1120, d922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8792 p hg
    simpa only [d4395, d1120, d922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8874 (p : Pattern) (guard : d0 p = 1) : d1121 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8875 (p : Pattern) (guard : d4670 p = 1) : d1122 p ≤ (0 : Int) + d923 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1122, d923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8873 p hg
    simpa only [d4670, d1122, d923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1122, d923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8874 p hg
    simpa only [d4670, d1122, d923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8876 (p : Pattern) (guard : d4670 p = 1) : d1123 p ≤ (0 : Int) + d924 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1123, d924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8872 p hg
    simpa only [d1123, d924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1123, d924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8875 p hg
    simpa only [d1123, d924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8877 (p : Pattern) (guard : d0 p = 1) : d1124 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8878 (p : Pattern) (guard : d4670 p = 1) : d1125 p ≤ (0 : Int) + d915 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1125, d915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8863 p hg
    simpa only [d4670, d1125, d915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1125, d915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8877 p hg
    simpa only [d4670, d1125, d915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8879 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d300 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8880 (p : Pattern) (guard : d4395 p = 1) : d1124 p ≤ (0 : Int) + d926 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1124, d926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6637 p hg
    simpa only [d4395, d1124, d926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1124, d926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8879 p hg
    simpa only [d4395, d1124, d926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8881 (p : Pattern) (guard : d0 p = 1) : d1129 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8882 (p : Pattern) (guard : d4670 p = 1) : d1130 p ≤ (0 : Int) + d927 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1130, d927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8880 p hg
    simpa only [d4670, d1130, d927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1130, d927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8881 p hg
    simpa only [d4670, d1130, d927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8883 (p : Pattern) (guard : d4670 p = 1) : d1131 p ≤ (0 : Int) + d928 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1131, d928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8878 p hg
    simpa only [d1131, d928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1131, d928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8882 p hg
    simpa only [d1131, d928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8884 (p : Pattern) (guard : d4670 p = 1) : d1132 p ≤ (0 : Int) + d929 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1132, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8876 p hg
    simpa only [d1132, d929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1132, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8883 p hg
    simpa only [d1132, d929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8885 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d241 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8886 (p : Pattern) (guard : d4395 p = 1) : d1089 p ≤ (0 : Int) + d242 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1089, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4395, d1089, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1089, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8885 p hg
    simpa only [d4395, d1089, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8887 (p : Pattern) (guard : d0 p = 1) : d1134 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8888 (p : Pattern) (guard : d4670 p = 1) : d1135 p ≤ (0 : Int) + d930 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1135, d930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8886 p hg
    simpa only [d4670, d1135, d930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1135, d930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8887 p hg
    simpa only [d4670, d1135, d930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8889 (p : Pattern) (guard : d4395 p = 1) : d1061 p ≤ (0 : Int) + d245 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1061, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4395, d1061, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1061, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8862 p hg
    simpa only [d4395, d1061, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8890 (p : Pattern) (guard : d4670 p = 1) : d1062 p ≤ (0 : Int) + d931 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1062, d931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8889 p hg
    simpa only [d4670, d1062, d931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1062, d931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4670, d1062, d931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8891 (p : Pattern) (guard : d4670 p = 1) : d1136 p ≤ (0 : Int) + d932 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1136, d932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8888 p hg
    simpa only [d1136, d932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1136, d932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8890 p hg
    simpa only [d1136, d932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8892 (p : Pattern) (guard : d0 p = 1) : d1138 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8893 (p : Pattern) (guard : d4670 p = 1) : d1139 p ≤ (0 : Int) + d931 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1139, d931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8889 p hg
    simpa only [d4670, d1139, d931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1139, d931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8892 p hg
    simpa only [d4670, d1139, d931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8894 (p : Pattern) (guard : d4395 p = 1) : d1140 p ≤ (0 : Int) + d933 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1140, d933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2371 p hg
    simpa only [d4395, d1140, d933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1140, d933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8800 p hg
    simpa only [d4395, d1140, d933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8895 (p : Pattern) (guard : d4670 p = 1) : d1141 p ≤ (0 : Int) + d934 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1141, d934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8894 p hg
    simpa only [d4670, d1141, d934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1141, d934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4670, d1141, d934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8896 (p : Pattern) (guard : d4670 p = 1) : d1142 p ≤ (0 : Int) + d935 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1142, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8893 p hg
    simpa only [d1142, d935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1142, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8895 p hg
    simpa only [d1142, d935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8897 (p : Pattern) (guard : d4670 p = 1) : d1143 p ≤ (0 : Int) + d936 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1143, d936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8891 p hg
    simpa only [d1143, d936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1143, d936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8896 p hg
    simpa only [d1143, d936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8898 (p : Pattern) (guard : d4670 p = 1) : d1144 p ≤ (0 : Int) + d937 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1144, d937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8884 p hg
    simpa only [d1144, d937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1144, d937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8897 p hg
    simpa only [d1144, d937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8899 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d252 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8900 (p : Pattern) (guard : d4395 p = 1) : d1089 p ≤ (0 : Int) + d253 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1089, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4395, d1089, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1089, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8899 p hg
    simpa only [d4395, d1089, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8901 (p : Pattern) (guard : d4670 p = 1) : d1135 p ≤ (0 : Int) + d938 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1135, d938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8900 p hg
    simpa only [d4670, d1135, d938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1135, d938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8887 p hg
    simpa only [d4670, d1135, d938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8902 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d136 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8903 (p : Pattern) (guard : d4395 p = 1) : d1061 p ≤ (0 : Int) + d939 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1061, d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4395, d1061, d939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1061, d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8902 p hg
    simpa only [d4395, d1061, d939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8904 (p : Pattern) (guard : d4670 p = 1) : d1062 p ≤ (0 : Int) + d940 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d1062, d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8903 p hg
    simpa only [d4670, d1062, d940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d1062, d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4670, d1062, d940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8905 (p : Pattern) (guard : d4670 p = 1) : d1136 p ≤ (0 : Int) + d941 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1136, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8901 p hg
    simpa only [d1136, d941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1136, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8904 p hg
    simpa only [d1136, d941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8906 (p : Pattern) (guard : d4670 p = 1) : d1143 p ≤ (0 : Int) + d942 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1143, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8905 p hg
    simpa only [d1143, d942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1143, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8896 p hg
    simpa only [d1143, d942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8907 (p : Pattern) (guard : d4670 p = 1) : d1145 p ≤ (0 : Int) + d943 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1145, d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8906 p hg
    simpa only [d1145, d943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1145, d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6484 p hg
    simpa only [d1145, d943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8908 (p : Pattern) (guard : d4670 p = 1) : d1146 p ≤ (0 : Int) + d944 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1146, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8898 p hg
    simpa only [d1146, d944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1146, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8907 p hg
    simpa only [d1146, d944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8909 (p : Pattern) (guard : d4670 p = 1) : d1147 p ≤ (0 : Int) + d945 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1147, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8870 p hg
    simpa only [d1147, d945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1147, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8908 p hg
    simpa only [d1147, d945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8910 (p : Pattern) (guard : d4670 p = 1) : d1148 p ≤ (0 : Int) + d946 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1148, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8741 p hg
    simpa only [d1148, d946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1148, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8909 p hg
    simpa only [d1148, d946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8911 (p : Pattern) (guard : d4670 p = 1) : d1149 p ≤ (0 : Int) + d947 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1149, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8855 p hg
    simpa only [d1149, d947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1149, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8910 p hg
    simpa only [d1149, d947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8912 (p : Pattern) (guard : d4670 p = 1) : d1150 p ≤ (0 : Int) + d948 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d1150, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8836 p hg
    simpa only [d1150, d948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d1150, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8911 p hg
    simpa only [d1150, d948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8913 (p : Pattern) (guard : d0 p = 1) : d949 p ≤ (0 : Int) + d791 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8914 (p : Pattern) (guard : d1 p = 1) : d950 p ≤ (0 : Int) + d33 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1998 p hg
    simpa only [d950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8915 (p : Pattern) (guard : d0 p = 1) : d361 p ≤ (0 : Int) + d79 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8916 (p : Pattern) (guard : d4395 p = 1) : d951 p ≤ (0 : Int) + d791 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d951, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8914 p hg
    simpa only [d4395, d951, d791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d951, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8915 p hg
    simpa only [d4395, d951, d791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8917 (p : Pattern) (guard : d4617 p = 1) : d952 p ≤ (0 : Int) + d791 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8913 p hg
    simpa only [d4617, d952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8916 p hg
    simpa only [d4617, d952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8918 (p : Pattern) (guard : d0 p = 1) : d955 p ≤ (0 : Int) + d791 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8919 (p : Pattern) (guard : d4618 p = 1) : d956 p ≤ (0 : Int) + d791 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8917 p hg
    simpa only [d4618, d956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8918 p hg
    simpa only [d4618, d956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8920 (p : Pattern) (guard : d0 p = 1) : d957 p ≤ (0 : Int) + d799 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8921 (p : Pattern) (guard : d0 p = 1) : d374 p ≤ (0 : Int) + d798 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8922 (p : Pattern) (guard : d4395 p = 1) : d958 p ≤ (0 : Int) + d799 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d958, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6412 p hg
    simpa only [d4395, d958, d799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d958, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8921 p hg
    simpa only [d4395, d958, d799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8923 (p : Pattern) (guard : d4617 p = 1) : d959 p ≤ (0 : Int) + d799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8920 p hg
    simpa only [d4617, d959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8922 p hg
    simpa only [d4617, d959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8924 (p : Pattern) (guard : d0 p = 1) : d962 p ≤ (0 : Int) + d799 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8925 (p : Pattern) (guard : d4618 p = 1) : d963 p ≤ (0 : Int) + d799 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8923 p hg
    simpa only [d4618, d963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8924 p hg
    simpa only [d4618, d963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8926 (p : Pattern) (guard : d4618 p = 1) : d964 p ≤ (0 : Int) + d4766 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d964, d4766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8919 p hg
    simpa only [d964, d4766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d964, d4766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8925 p hg
    simpa only [d964, d4766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8927 (p : Pattern) (guard : d0 p = 1) : d965 p ≤ (0 : Int) + d804 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8928 (p : Pattern) (guard : d4395 p = 1) : d966 p ≤ (0 : Int) + d804 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d966, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare846 p hg
    simpa only [d4395, d966, d804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d966, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8687 p hg
    simpa only [d4395, d966, d804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8929 (p : Pattern) (guard : d4617 p = 1) : d967 p ≤ (0 : Int) + d804 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8927 p hg
    simpa only [d4617, d967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8928 p hg
    simpa only [d4617, d967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8930 (p : Pattern) (guard : d0 p = 1) : d969 p ≤ (0 : Int) + d804 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8931 (p : Pattern) (guard : d4618 p = 1) : d970 p ≤ (0 : Int) + d804 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8929 p hg
    simpa only [d4618, d970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8930 p hg
    simpa only [d4618, d970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8932 (p : Pattern) (guard : d0 p = 1) : d971 p ≤ (0 : Int) + d810 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8933 (p : Pattern) (guard : d4617 p = 1) : d973 p ≤ (0 : Int) + d810 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8932 p hg
    simpa only [d4617, d973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8696 p hg
    simpa only [d4617, d973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8934 (p : Pattern) (guard : d0 p = 1) : d974 p ≤ (0 : Int) + d810 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8935 (p : Pattern) (guard : d4618 p = 1) : d975 p ≤ (0 : Int) + d810 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8933 p hg
    simpa only [d4618, d975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8934 p hg
    simpa only [d4618, d975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8936 (p : Pattern) (guard : d4618 p = 1) : d976 p ≤ (0 : Int) + d4767 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d976, d4767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8931 p hg
    simpa only [d976, d4767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d976, d4767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8935 p hg
    simpa only [d976, d4767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8937 (p : Pattern) (guard : d4618 p = 1) : d977 p ≤ (0 : Int) + d4768 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d977, d4768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8926 p hg
    simpa only [d977, d4768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d977, d4768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8936 p hg
    simpa only [d977, d4768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8938 (p : Pattern) (guard : d0 p = 1) : d978 p ≤ (0 : Int) + d804 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8939 (p : Pattern) (guard : d4617 p = 1) : d979 p ≤ (0 : Int) + d804 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8938 p hg
    simpa only [d4617, d979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8928 p hg
    simpa only [d4617, d979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8940 (p : Pattern) (guard : d4618 p = 1) : d980 p ≤ (0 : Int) + d804 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8939 p hg
    simpa only [d4618, d980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8930 p hg
    simpa only [d4618, d980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8941 (p : Pattern) (guard : d0 p = 1) : d981 p ≤ (0 : Int) + d810 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8942 (p : Pattern) (guard : d4617 p = 1) : d982 p ≤ (0 : Int) + d810 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8941 p hg
    simpa only [d4617, d982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8696 p hg
    simpa only [d4617, d982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8943 (p : Pattern) (guard : d4618 p = 1) : d983 p ≤ (0 : Int) + d810 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8942 p hg
    simpa only [d4618, d983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8934 p hg
    simpa only [d4618, d983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8944 (p : Pattern) (guard : d4618 p = 1) : d984 p ≤ (0 : Int) + d4767 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d984, d4767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8940 p hg
    simpa only [d984, d4767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d984, d4767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8943 p hg
    simpa only [d984, d4767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8945 (p : Pattern) (guard : d0 p = 1) : d985 p ≤ (0 : Int) + d91 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8946 (p : Pattern) (guard : d4617 p = 1) : d986 p ≤ (0 : Int) + d91 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8945 p hg
    simpa only [d4617, d986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7838 p hg
    simpa only [d4617, d986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8947 (p : Pattern) (guard : d0 p = 1) : d93 p ≤ (0 : Int) + d91 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8948 (p : Pattern) (guard : d4618 p = 1) : d987 p ≤ (0 : Int) + d91 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8946 p hg
    simpa only [d4618, d987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8947 p hg
    simpa only [d4618, d987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8949 (p : Pattern) (guard : d4617 p = 1) : d93 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5894 p hg
    simpa only [d4617, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7817 p hg
    simpa only [d4617, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8950 (p : Pattern) (guard : d4618 p = 1) : d95 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8949 p hg
    simpa only [d4618, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4618, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8951 (p : Pattern) (guard : d4618 p = 1) : d988 p ≤ (0 : Int) + d4434 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d988, d4434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8948 p hg
    simpa only [d988, d4434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d988, d4434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8950 p hg
    simpa only [d988, d4434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8952 (p : Pattern) (guard : d4618 p = 1) : d989 p ≤ (0 : Int) + d4769 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d989, d4769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8944 p hg
    simpa only [d989, d4769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d989, d4769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8951 p hg
    simpa only [d989, d4769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8953 (p : Pattern) (guard : d4618 p = 1) : d990 p ≤ (0 : Int) + d4770 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d990, d4770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8937 p hg
    simpa only [d990, d4770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d990, d4770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8952 p hg
    simpa only [d990, d4770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8954 (p : Pattern) (guard : d0 p = 1) : d991 p ≤ (0 : Int) + d791 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8955 (p : Pattern) (guard : d4395 p = 1) : d992 p ≤ (0 : Int) + d791 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d992, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8914 p hg
    simpa only [d4395, d992, d791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d992, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8687 p hg
    simpa only [d4395, d992, d791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8956 (p : Pattern) (guard : d4617 p = 1) : d993 p ≤ (0 : Int) + d791 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8954 p hg
    simpa only [d4617, d993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8955 p hg
    simpa only [d4617, d993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8957 (p : Pattern) (guard : d0 p = 1) : d995 p ≤ (0 : Int) + d791 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8958 (p : Pattern) (guard : d4618 p = 1) : d996 p ≤ (0 : Int) + d791 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8956 p hg
    simpa only [d4618, d996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8957 p hg
    simpa only [d4618, d996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8959 (p : Pattern) (guard : d0 p = 1) : d997 p ≤ (0 : Int) + d799 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
