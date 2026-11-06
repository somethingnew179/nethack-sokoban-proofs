/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons046
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare6580 (p : Pattern) (guard : d4670 p = 1) : d886 p ≤ (0 : Int) + d1086 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d886, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6578 p hg
    simpa only [d4670, d886, d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d886, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6579 p hg
    simpa only [d4670, d886, d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6581 (p : Pattern) (guard : d4670 p = 1) : d887 p ≤ (0 : Int) + d1087 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d887, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6580 p hg
    simpa only [d887, d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d887, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6538 p hg
    simpa only [d887, d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6582 (p : Pattern) (guard : d4670 p = 1) : d888 p ≤ (0 : Int) + d1088 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d888, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6576 p hg
    simpa only [d888, d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d888, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6581 p hg
    simpa only [d888, d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6583 (p : Pattern) (guard : d4395 p = 1) : d111 p ≤ (0 : Int) + d1089 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d111, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4395, d111, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d111, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4358 p hg
    simpa only [d4395, d111, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6584 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1059 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6585 (p : Pattern) (guard : d4670 p = 1) : d889 p ≤ (0 : Int) + d1090 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d889, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6583 p hg
    simpa only [d4670, d889, d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d889, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6584 p hg
    simpa only [d4670, d889, d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6586 (p : Pattern) (guard : d4670 p = 1) : d890 p ≤ (0 : Int) + d1091 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d890, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6585 p hg
    simpa only [d890, d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d890, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6546 p hg
    simpa only [d890, d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6587 (p : Pattern) (guard : d4670 p = 1) : d891 p ≤ (0 : Int) + d1092 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d891, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6586 p hg
    simpa only [d891, d1092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d891, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6556 p hg
    simpa only [d891, d1092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6588 (p : Pattern) (guard : d4670 p = 1) : d892 p ≤ (0 : Int) + d1093 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d892, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6582 p hg
    simpa only [d892, d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d892, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6587 p hg
    simpa only [d892, d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6589 (p : Pattern) (guard : d4670 p = 1) : d893 p ≤ (0 : Int) + d1094 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d893, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6587 p hg
    simpa only [d893, d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d893, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6484 p hg
    simpa only [d893, d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6590 (p : Pattern) (guard : d4670 p = 1) : d894 p ≤ (0 : Int) + d1095 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d894, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6588 p hg
    simpa only [d894, d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d894, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6589 p hg
    simpa only [d894, d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6591 (p : Pattern) (guard : d4670 p = 1) : d895 p ≤ (0 : Int) + d1096 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d895, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6570 p hg
    simpa only [d895, d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d895, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6590 p hg
    simpa only [d895, d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6592 (p : Pattern) (guard : d4670 p = 1) : d896 p ≤ (0 : Int) + d1097 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d896, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6487 p hg
    simpa only [d896, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d896, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6591 p hg
    simpa only [d896, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6593 (p : Pattern) (guard : d4670 p = 1) : d897 p ≤ (0 : Int) + d1098 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d897, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6520 p hg
    simpa only [d897, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d897, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6592 p hg
    simpa only [d897, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6594 (p : Pattern) (guard : d4395 p = 1) : d188 p ≤ (0 : Int) + d1001 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d188, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4395, d188, d1001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d188, d1001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6422 p hg
    simpa only [d4395, d188, d1001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6595 (p : Pattern) (guard : d4670 p = 1) : d898 p ≤ (0 : Int) + d1002 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d898, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6594 p hg
    simpa only [d4670, d898, d1002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d898, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6471 p hg
    simpa only [d4670, d898, d1002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6596 (p : Pattern) (guard : d0 p = 1) : d194 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6597 (p : Pattern) (guard : d4395 p = 1) : d899 p ≤ (0 : Int) + d968 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d899, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4395, d899, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d899, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6596 p hg
    simpa only [d4395, d899, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6598 (p : Pattern) (guard : d4670 p = 1) : d900 p ≤ (0 : Int) + d969 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d900, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6597 p hg
    simpa only [d4670, d900, d969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d900, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4670, d900, d969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6599 (p : Pattern) (guard : d4670 p = 1) : d901 p ≤ (0 : Int) + d1003 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d901, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6595 p hg
    simpa only [d901, d1003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d901, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6598 p hg
    simpa only [d901, d1003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6600 (p : Pattern) (guard : d0 p = 1) : d198 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6601 (p : Pattern) (guard : d4395 p = 1) : d199 p ≤ (0 : Int) + d968 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d199, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4395, d199, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d199, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6600 p hg
    simpa only [d4395, d199, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6602 (p : Pattern) (guard : d4670 p = 1) : d902 p ≤ (0 : Int) + d1099 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d902, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6601 p hg
    simpa only [d4670, d902, d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d902, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6428 p hg
    simpa only [d4670, d902, d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6603 (p : Pattern) (guard : d0 p = 1) : d83 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6604 (p : Pattern) (guard : d4395 p = 1) : d903 p ≤ (0 : Int) + d1100 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d903, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare847 p hg
    simpa only [d4395, d903, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d903, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6603 p hg
    simpa only [d4395, d903, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6605 (p : Pattern) (guard : d4670 p = 1) : d904 p ≤ (0 : Int) + d1101 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d904, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6604 p hg
    simpa only [d4670, d904, d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d904, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4670, d904, d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6606 (p : Pattern) (guard : d4670 p = 1) : d905 p ≤ (0 : Int) + d1102 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d905, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6602 p hg
    simpa only [d905, d1102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d905, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6605 p hg
    simpa only [d905, d1102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6607 (p : Pattern) (guard : d4670 p = 1) : d906 p ≤ (0 : Int) + d1103 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d906, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6599 p hg
    simpa only [d906, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d906, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6606 p hg
    simpa only [d906, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6608 (p : Pattern) (guard : d4670 p = 1) : d907 p ≤ (0 : Int) + d1104 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d907, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6515 p hg
    simpa only [d907, d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d907, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6607 p hg
    simpa only [d907, d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6609 (p : Pattern) (guard : d4670 p = 1) : d908 p ≤ (0 : Int) + d1105 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d908, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6607 p hg
    simpa only [d908, d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d908, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6484 p hg
    simpa only [d908, d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6610 (p : Pattern) (guard : d4670 p = 1) : d909 p ≤ (0 : Int) + d1106 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d909, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6608 p hg
    simpa only [d909, d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d909, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6609 p hg
    simpa only [d909, d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6611 (p : Pattern) (guard : d4670 p = 1) : d910 p ≤ (0 : Int) + d1107 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d910, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6508 p hg
    simpa only [d910, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d910, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6610 p hg
    simpa only [d910, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6612 (p : Pattern) (guard : d4670 p = 1) : d911 p ≤ (0 : Int) + d1108 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d911, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6487 p hg
    simpa only [d911, d1108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d911, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6611 p hg
    simpa only [d911, d1108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6613 (p : Pattern) (guard : d0 p = 1) : d211 p ≤ (0 : Int) + d448 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6614 (p : Pattern) (guard : d4395 p = 1) : d212 p ≤ (0 : Int) + d1109 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d212, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d212, d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d212, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6613 p hg
    simpa only [d4395, d212, d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6615 (p : Pattern) (guard : d0 p = 1) : d451 p ≤ (0 : Int) + d1051 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6616 (p : Pattern) (guard : d4670 p = 1) : d912 p ≤ (0 : Int) + d1110 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d912, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6614 p hg
    simpa only [d4670, d912, d1110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d912, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6615 p hg
    simpa only [d4670, d912, d1110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6617 (p : Pattern) (guard : d4670 p = 1) : d913 p ≤ (0 : Int) + d1111 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d913, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6616 p hg
    simpa only [d913, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d913, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6538 p hg
    simpa only [d913, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6618 (p : Pattern) (guard : d4670 p = 1) : d914 p ≤ (0 : Int) + d1112 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d914, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6528 p hg
    simpa only [d914, d1112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d914, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6617 p hg
    simpa only [d914, d1112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6619 (p : Pattern) (guard : d0 p = 1) : d211 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6620 (p : Pattern) (guard : d4395 p = 1) : d212 p ≤ (0 : Int) + d1059 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d212, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6529 p hg
    simpa only [d4395, d212, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d212, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6619 p hg
    simpa only [d4395, d212, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6621 (p : Pattern) (guard : d4670 p = 1) : d915 p ≤ (0 : Int) + d1065 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d915, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6620 p hg
    simpa only [d4670, d915, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d915, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6550 p hg
    simpa only [d4670, d915, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6622 (p : Pattern) (guard : d4670 p = 1) : d916 p ≤ (0 : Int) + d1067 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d916, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6621 p hg
    simpa only [d916, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d916, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6555 p hg
    simpa only [d916, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6623 (p : Pattern) (guard : d4670 p = 1) : d917 p ≤ (0 : Int) + d1068 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d917, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6547 p hg
    simpa only [d917, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d917, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6622 p hg
    simpa only [d917, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6624 (p : Pattern) (guard : d4670 p = 1) : d918 p ≤ (0 : Int) + d1113 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d918, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6618 p hg
    simpa only [d918, d1113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d918, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6623 p hg
    simpa only [d918, d1113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6625 (p : Pattern) (guard : d4670 p = 1) : d919 p ≤ (0 : Int) + d1114 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d919, d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6562 p hg
    simpa only [d919, d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d919, d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6622 p hg
    simpa only [d919, d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6626 (p : Pattern) (guard : d4670 p = 1) : d920 p ≤ (0 : Int) + d1115 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d920, d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6625 p hg
    simpa only [d920, d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d920, d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6568 p hg
    simpa only [d920, d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6627 (p : Pattern) (guard : d4670 p = 1) : d921 p ≤ (0 : Int) + d1116 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d921, d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6624 p hg
    simpa only [d921, d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d921, d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6626 p hg
    simpa only [d921, d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6628 (p : Pattern) (guard : d4395 p = 1) : d111 p ≤ (0 : Int) + d1117 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d111, d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4395, d111, d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d111, d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4390 p hg
    simpa only [d4395, d111, d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6629 (p : Pattern) (guard : d0 p = 1) : d403 p ≤ (0 : Int) + d1118 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6630 (p : Pattern) (guard : d4670 p = 1) : d884 p ≤ (0 : Int) + d1119 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d884, d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6628 p hg
    simpa only [d4670, d884, d1119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d884, d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6629 p hg
    simpa only [d4670, d884, d1119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6631 (p : Pattern) (guard : d4395 p = 1) : d922 p ≤ (0 : Int) + d1120 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d922, d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2440 p hg
    simpa only [d4395, d922, d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d922, d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6544 p hg
    simpa only [d4395, d922, d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6632 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1121 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6633 (p : Pattern) (guard : d4670 p = 1) : d923 p ≤ (0 : Int) + d1122 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d923, d1122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6631 p hg
    simpa only [d4670, d923, d1122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d923, d1122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6632 p hg
    simpa only [d4670, d923, d1122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6634 (p : Pattern) (guard : d4670 p = 1) : d924 p ≤ (0 : Int) + d1123 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d924, d1123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6630 p hg
    simpa only [d924, d1123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d924, d1123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6633 p hg
    simpa only [d924, d1123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6635 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1124 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6636 (p : Pattern) (guard : d4670 p = 1) : d915 p ≤ (0 : Int) + d1125 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d915, d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6620 p hg
    simpa only [d4670, d915, d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d915, d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6635 p hg
    simpa only [d4670, d915, d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6637 (p : Pattern) (guard : d1 p = 1) : d925 p ≤ (0 : Int) + d925 p := by
  omega
theorem compare6638 (p : Pattern) (guard : d0 p = 1) : d300 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6639 (p : Pattern) (guard : d4395 p = 1) : d926 p ≤ (0 : Int) + d1124 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d926, d1124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6637 p hg
    simpa only [d4395, d926, d1124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d926, d1124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6638 p hg
    simpa only [d4395, d926, d1124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6640 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1129 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6641 (p : Pattern) (guard : d4670 p = 1) : d927 p ≤ (0 : Int) + d1130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d927, d1130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6639 p hg
    simpa only [d4670, d927, d1130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d927, d1130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6640 p hg
    simpa only [d4670, d927, d1130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6642 (p : Pattern) (guard : d4670 p = 1) : d928 p ≤ (0 : Int) + d1131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d928, d1131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6636 p hg
    simpa only [d928, d1131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d928, d1131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6641 p hg
    simpa only [d928, d1131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6643 (p : Pattern) (guard : d4670 p = 1) : d929 p ≤ (0 : Int) + d1132 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d929, d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6634 p hg
    simpa only [d929, d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d929, d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6642 p hg
    simpa only [d929, d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6644 (p : Pattern) (guard : d0 p = 1) : d241 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6645 (p : Pattern) (guard : d4395 p = 1) : d242 p ≤ (0 : Int) + d1089 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d242, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4395, d242, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d242, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6644 p hg
    simpa only [d4395, d242, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6646 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1134 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6647 (p : Pattern) (guard : d4670 p = 1) : d930 p ≤ (0 : Int) + d1135 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d930, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6645 p hg
    simpa only [d4670, d930, d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d930, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6646 p hg
    simpa only [d4670, d930, d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6648 (p : Pattern) (guard : d4395 p = 1) : d245 p ≤ (0 : Int) + d1061 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d245, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4395, d245, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d245, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6619 p hg
    simpa only [d4395, d245, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6649 (p : Pattern) (guard : d4670 p = 1) : d931 p ≤ (0 : Int) + d1062 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d931, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6648 p hg
    simpa only [d4670, d931, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d931, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4670, d931, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6650 (p : Pattern) (guard : d4670 p = 1) : d932 p ≤ (0 : Int) + d1136 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d932, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6647 p hg
    simpa only [d932, d1136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d932, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6649 p hg
    simpa only [d932, d1136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6651 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6652 (p : Pattern) (guard : d4670 p = 1) : d931 p ≤ (0 : Int) + d1139 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d931, d1139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6648 p hg
    simpa only [d4670, d931, d1139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d931, d1139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6651 p hg
    simpa only [d4670, d931, d1139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6653 (p : Pattern) (guard : d4395 p = 1) : d933 p ≤ (0 : Int) + d1140 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d933, d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2371 p hg
    simpa only [d4395, d933, d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d933, d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6553 p hg
    simpa only [d4395, d933, d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6654 (p : Pattern) (guard : d4670 p = 1) : d934 p ≤ (0 : Int) + d1141 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d934, d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6653 p hg
    simpa only [d4670, d934, d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d934, d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4670, d934, d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6655 (p : Pattern) (guard : d4670 p = 1) : d935 p ≤ (0 : Int) + d1142 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d935, d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6652 p hg
    simpa only [d935, d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d935, d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6654 p hg
    simpa only [d935, d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6656 (p : Pattern) (guard : d4670 p = 1) : d936 p ≤ (0 : Int) + d1143 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d936, d1143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6650 p hg
    simpa only [d936, d1143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d936, d1143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6655 p hg
    simpa only [d936, d1143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6657 (p : Pattern) (guard : d4670 p = 1) : d937 p ≤ (0 : Int) + d1144 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d937, d1144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6643 p hg
    simpa only [d937, d1144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d937, d1144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6656 p hg
    simpa only [d937, d1144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6658 (p : Pattern) (guard : d0 p = 1) : d252 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6659 (p : Pattern) (guard : d4395 p = 1) : d253 p ≤ (0 : Int) + d1089 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d253, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4395, d253, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d253, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6658 p hg
    simpa only [d4395, d253, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6660 (p : Pattern) (guard : d4670 p = 1) : d938 p ≤ (0 : Int) + d1135 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d938, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6659 p hg
    simpa only [d4670, d938, d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d938, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6646 p hg
    simpa only [d4670, d938, d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6661 (p : Pattern) (guard : d0 p = 1) : d136 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6662 (p : Pattern) (guard : d4395 p = 1) : d939 p ≤ (0 : Int) + d1061 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d939, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4395, d939, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d939, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6661 p hg
    simpa only [d4395, d939, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6663 (p : Pattern) (guard : d4670 p = 1) : d940 p ≤ (0 : Int) + d1062 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d4670, d940, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6662 p hg
    simpa only [d4670, d940, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4670, d940, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4670, d940, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6664 (p : Pattern) (guard : d4670 p = 1) : d941 p ≤ (0 : Int) + d1136 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d941, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6660 p hg
    simpa only [d941, d1136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d941, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6663 p hg
    simpa only [d941, d1136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6665 (p : Pattern) (guard : d4670 p = 1) : d942 p ≤ (0 : Int) + d1143 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d942, d1143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6664 p hg
    simpa only [d942, d1143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d942, d1143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6655 p hg
    simpa only [d942, d1143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6666 (p : Pattern) (guard : d4670 p = 1) : d943 p ≤ (0 : Int) + d1145 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d943, d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6665 p hg
    simpa only [d943, d1145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d943, d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6484 p hg
    simpa only [d943, d1145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6667 (p : Pattern) (guard : d4670 p = 1) : d944 p ≤ (0 : Int) + d1146 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d944, d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6657 p hg
    simpa only [d944, d1146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d944, d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6666 p hg
    simpa only [d944, d1146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6668 (p : Pattern) (guard : d4670 p = 1) : d945 p ≤ (0 : Int) + d1147 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d945, d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6627 p hg
    simpa only [d945, d1147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d945, d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6667 p hg
    simpa only [d945, d1147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6669 (p : Pattern) (guard : d4670 p = 1) : d946 p ≤ (0 : Int) + d1148 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d946, d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6487 p hg
    simpa only [d946, d1148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d946, d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6668 p hg
    simpa only [d946, d1148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6670 (p : Pattern) (guard : d4670 p = 1) : d947 p ≤ (0 : Int) + d1149 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d947, d1149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6612 p hg
    simpa only [d947, d1149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d947, d1149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6669 p hg
    simpa only [d947, d1149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6671 (p : Pattern) (guard : d4670 p = 1) : d948 p ≤ (0 : Int) + d1150 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4670 p = 1 := by simpa only [d948, d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6593 p hg
    simpa only [d948, d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4670 p = 1 := by simpa only [d948, d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6670 p hg
    simpa only [d948, d1150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6672 (p : Pattern) (guard : d0 p = 1) : d16 p ≤ (2 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6673 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (2 : Int) + d16 p := by
  omega
theorem compare6674 (p : Pattern) (guard : d0 p = 1) : d20 p ≤ (2 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6675 (p : Pattern) (guard : d4148 p = 1) : d21 p ≤ (2 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6673 p hg
    simpa only [d4148, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6674 p hg
    simpa only [d4148, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6676 (p : Pattern) (guard : d4672 p = 1) : d22 p ≤ (2 : Int) + d16 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6672 p hg
    simpa only [d4672, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6675 p hg
    simpa only [d4672, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6677 (p : Pattern) (guard : d0 p = 1) : d362 p ≤ (2 : Int) + d33 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6678 (p : Pattern) (guard : d4673 p = 1) : d790 p ≤ (2 : Int) + d4674 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d790, d4674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6676 p hg
    simpa only [d4673, d790, d4674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d790, d4674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6677 p hg
    simpa only [d4673, d790, d4674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6679 (p : Pattern) (guard : d0 p = 1) : d33 p ≤ (2 : Int) + d33 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6680 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (2 : Int) + d32 p := by
  omega
theorem compare6681 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (2 : Int) + d33 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d53, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4691 p hg
    simpa only [d53, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d53, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6680 p hg
    simpa only [d53, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6682 (p : Pattern) (guard : d0 p = 1) : d78 p ≤ (2 : Int) + d33 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6683 (p : Pattern) (guard : d4148 p = 1) : d79 p ≤ (2 : Int) + d33 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6681 p hg
    simpa only [d4148, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6682 p hg
    simpa only [d4148, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6684 (p : Pattern) (guard : d4672 p = 1) : d791 p ≤ (2 : Int) + d33 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6679 p hg
    simpa only [d4672, d791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6683 p hg
    simpa only [d4672, d791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6685 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (2 : Int) + d43 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6686 (p : Pattern) (guard : d4673 p = 1) : d792 p ≤ (2 : Int) + d4675 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d792, d4675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6684 p hg
    simpa only [d4673, d792, d4675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d792, d4675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6685 p hg
    simpa only [d4673, d792, d4675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6687 (p : Pattern) (guard : d4673 p = 1) : d793 p ≤ (2 : Int) + d4676 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d793, d4676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6678 p hg
    simpa only [d793, d4676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d793, d4676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6686 p hg
    simpa only [d793, d4676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6688 (p : Pattern) (guard : d0 p = 1) : d54 p ≤ (2 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6689 (p : Pattern) (guard : d0 p = 1) : d26 p ≤ (2 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6690 (p : Pattern) (guard : d4148 p = 1) : d55 p ≤ (2 : Int) + d53 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4869 p hg
    simpa only [d4148, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6689 p hg
    simpa only [d4148, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6691 (p : Pattern) (guard : d4672 p = 1) : d56 p ≤ (2 : Int) + d53 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6688 p hg
    simpa only [d4672, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6690 p hg
    simpa only [d4672, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6692 (p : Pattern) (guard : d0 p = 1) : d387 p ≤ (2 : Int) + d795 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6693 (p : Pattern) (guard : d4673 p = 1) : d794 p ≤ (2 : Int) + d4677 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d794, d4677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6691 p hg
    simpa only [d4673, d794, d4677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d794, d4677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6692 p hg
    simpa only [d4673, d794, d4677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6694 (p : Pattern) (guard : d0 p = 1) : d796 p ≤ (2 : Int) + d795 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6695 (p : Pattern) (guard : d1 p = 1) : d797 p ≤ (2 : Int) + d795 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d797, d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4867 p hg
    simpa only [d797, d795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d797, d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4700 p hg
    simpa only [d797, d795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6696 (p : Pattern) (guard : d0 p = 1) : d62 p ≤ (2 : Int) + d795 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6697 (p : Pattern) (guard : d4148 p = 1) : d798 p ≤ (2 : Int) + d795 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6695 p hg
    simpa only [d4148, d798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6696 p hg
    simpa only [d4148, d798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6698 (p : Pattern) (guard : d4672 p = 1) : d799 p ≤ (2 : Int) + d795 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6694 p hg
    simpa only [d4672, d799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6697 p hg
    simpa only [d4672, d799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6699 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d173 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6700 (p : Pattern) (guard : d4673 p = 1) : d800 p ≤ (2 : Int) + d4678 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d800, d4678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6698 p hg
    simpa only [d4673, d800, d4678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d800, d4678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6699 p hg
    simpa only [d4673, d800, d4678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6701 (p : Pattern) (guard : d4673 p = 1) : d801 p ≤ (2 : Int) + d4679 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d801, d4679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6693 p hg
    simpa only [d801, d4679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d801, d4679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6700 p hg
    simpa only [d801, d4679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6702 (p : Pattern) (guard : d4673 p = 1) : d802 p ≤ (2 : Int) + d4680 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d802, d4680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6687 p hg
    simpa only [d802, d4680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d802, d4680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6701 p hg
    simpa only [d802, d4680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6703 (p : Pattern) (guard : d0 p = 1) : d394 p ≤ (2 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6704 (p : Pattern) (guard : d4673 p = 1) : d803 p ≤ (2 : Int) + d4681 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d803, d4681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6676 p hg
    simpa only [d4673, d803, d4681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d803, d4681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6703 p hg
    simpa only [d4673, d803, d4681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6705 (p : Pattern) (guard : d0 p = 1) : d53 p ≤ (2 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6706 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (2 : Int) + d53 p := by
  omega
theorem compare6707 (p : Pattern) (guard : d0 p = 1) : d78 p ≤ (2 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6708 (p : Pattern) (guard : d4148 p = 1) : d79 p ≤ (2 : Int) + d53 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6706 p hg
    simpa only [d4148, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6707 p hg
    simpa only [d4148, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6709 (p : Pattern) (guard : d4672 p = 1) : d804 p ≤ (2 : Int) + d53 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6705 p hg
    simpa only [d4672, d804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6708 p hg
    simpa only [d4672, d804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6710 (p : Pattern) (guard : d4673 p = 1) : d805 p ≤ (2 : Int) + d4682 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d805, d4682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6709 p hg
    simpa only [d4673, d805, d4682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d805, d4682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4673, d805, d4682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6711 (p : Pattern) (guard : d4673 p = 1) : d806 p ≤ (2 : Int) + d4683 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d806, d4683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6704 p hg
    simpa only [d806, d4683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d806, d4683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6710 p hg
    simpa only [d806, d4683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6712 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6713 (p : Pattern) (guard : d4673 p = 1) : d807 p ≤ (2 : Int) + d4684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d807, d4684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6691 p hg
    simpa only [d4673, d807, d4684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d807, d4684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6712 p hg
    simpa only [d4673, d807, d4684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6714 (p : Pattern) (guard : d0 p = 1) : d808 p ≤ (2 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6715 (p : Pattern) (guard : d0 p = 1) : d62 p ≤ (2 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6716 (p : Pattern) (guard : d4148 p = 1) : d809 p ≤ (2 : Int) + d20 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4741 p hg
    simpa only [d4148, d809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6715 p hg
    simpa only [d4148, d809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6717 (p : Pattern) (guard : d4672 p = 1) : d810 p ≤ (2 : Int) + d20 p := by
  cases selected : p 162 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4672, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6714 p hg
    simpa only [d4672, d810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4672, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6716 p hg
    simpa only [d4672, d810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6718 (p : Pattern) (guard : d4673 p = 1) : d811 p ≤ (2 : Int) + d4685 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4672 p = 1 := by simpa only [d4673, d811, d4685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6717 p hg
    simpa only [d4673, d811, d4685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4673, d811, d4685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4673, d811, d4685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6719 (p : Pattern) (guard : d4673 p = 1) : d812 p ≤ (2 : Int) + d4686 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4673 p = 1 := by simpa only [d812, d4686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6713 p hg
    simpa only [d812, d4686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4673 p = 1 := by simpa only [d812, d4686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6718 p hg
    simpa only [d812, d4686, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
