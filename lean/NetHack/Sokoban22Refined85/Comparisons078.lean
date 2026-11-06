/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons077
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare10920 (p : Pattern) (guard : d4765 p = 1) : d1426 p ≤ (0 : Int) + d4860 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1426, d4860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10862 p hg
    simpa only [d1426, d4860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1426, d4860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10919 p hg
    simpa only [d1426, d4860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10921 (p : Pattern) (guard : d4765 p = 1) : d1427 p ≤ (0 : Int) + d4864 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1427, d4864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10920 p hg
    simpa only [d1427, d4864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1427, d4864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10904 p hg
    simpa only [d1427, d4864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10922 (p : Pattern) (guard : d4765 p = 1) : d1428 p ≤ (0 : Int) + d4867 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1428, d4867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10904 p hg
    simpa only [d1428, d4867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1428, d4867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10892 p hg
    simpa only [d1428, d4867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10923 (p : Pattern) (guard : d4765 p = 1) : d1429 p ≤ (0 : Int) + d4868 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1429, d4868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10921 p hg
    simpa only [d1429, d4868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1429, d4868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10922 p hg
    simpa only [d1429, d4868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10924 (p : Pattern) (guard : d4765 p = 1) : d1430 p ≤ (0 : Int) + d4869 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1430, d4869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10917 p hg
    simpa only [d1430, d4869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1430, d4869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10923 p hg
    simpa only [d1430, d4869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10925 (p : Pattern) (guard : d0 p = 1) : d1167 p ≤ (0 : Int) + d53 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10926 (p : Pattern) (guard : d4765 p = 1) : d1431 p ≤ (0 : Int) + d53 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10864 p hg
    simpa only [d4765, d1431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10925 p hg
    simpa only [d4765, d1431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10927 (p : Pattern) (guard : d4765 p = 1) : d1432 p ≤ (0 : Int) + d4857 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1432, d4857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10926 p hg
    simpa only [d1432, d4857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1432, d4857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10871 p hg
    simpa only [d1432, d4857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10928 (p : Pattern) (guard : d4765 p = 1) : d1433 p ≤ (0 : Int) + d4859 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1433, d4859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10927 p hg
    simpa only [d1433, d4859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1433, d4859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10883 p hg
    simpa only [d1433, d4859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10929 (p : Pattern) (guard : d4765 p = 1) : d1434 p ≤ (0 : Int) + d4860 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1434, d4860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10862 p hg
    simpa only [d1434, d4860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1434, d4860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10928 p hg
    simpa only [d1434, d4860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10930 (p : Pattern) (guard : d4765 p = 1) : d1435 p ≤ (0 : Int) + d4864 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1435, d4864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10929 p hg
    simpa only [d1435, d4864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1435, d4864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10904 p hg
    simpa only [d1435, d4864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10931 (p : Pattern) (guard : d4765 p = 1) : d1436 p ≤ (0 : Int) + d4866 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1436, d4866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10930 p hg
    simpa only [d1436, d4866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1436, d4866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10916 p hg
    simpa only [d1436, d4866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10932 (p : Pattern) (guard : d4765 p = 1) : d1437 p ≤ (0 : Int) + d4869 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1437, d4869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10931 p hg
    simpa only [d1437, d4869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1437, d4869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10923 p hg
    simpa only [d1437, d4869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10933 (p : Pattern) (guard : d4765 p = 1) : d1438 p ≤ (0 : Int) + d4869 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10924 p hg
    simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10932 p hg
    simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10934 (p : Pattern) (guard : d4147 p = 1) : d105 p ≤ (0 : Int) + d105 p := by
  omega
theorem compare10935 (p : Pattern) (guard : d0 p = 1) : d110 p ≤ (0 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10936 (p : Pattern) (guard : d4765 p = 1) : d111 p ≤ (0 : Int) + d105 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10934 p hg
    simpa only [d4765, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10935 p hg
    simpa only [d4765, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10937 (p : Pattern) (guard : d0 p = 1) : d105 p ≤ (0 : Int) + d60 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10938 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (0 : Int) + d10 p := by
  change (3 : Int) ≤ (0 : Int) + 10
  decide
theorem compare10939 (p : Pattern) (guard : d1 p = 1) : d115 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d115, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10938 p hg
    simpa only [d115, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d115, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d115, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10940 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (0 : Int) + d58 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d116, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10938 p hg
    simpa only [d116, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d116, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10939 p hg
    simpa only [d116, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10941 (p : Pattern) (guard : d1 p = 1) : d117 p ≤ (0 : Int) + d59 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d117, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10940 p hg
    simpa only [d117, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d117, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d117, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10942 (p : Pattern) (guard : d1 p = 1) : d118 p ≤ (0 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d118, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1585 p hg
    simpa only [d118, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d118, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10941 p hg
    simpa only [d118, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10943 (p : Pattern) (guard : d4147 p = 1) : d1043 p ≤ (0 : Int) + d60 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10937 p hg
    simpa only [d4147, d1043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10942 p hg
    simpa only [d4147, d1043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10944 (p : Pattern) (guard : d0 p = 1) : d112 p ≤ (0 : Int) + d60 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10945 (p : Pattern) (guard : d4765 p = 1) : d1439 p ≤ (0 : Int) + d60 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10943 p hg
    simpa only [d4765, d1439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10944 p hg
    simpa only [d4765, d1439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10946 (p : Pattern) (guard : d4765 p = 1) : d1440 p ≤ (0 : Int) + d4870 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1440, d4870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10936 p hg
    simpa only [d1440, d4870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1440, d4870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10945 p hg
    simpa only [d1440, d4870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10947 (p : Pattern) (guard : d0 p = 1) : d118 p ≤ (0 : Int) + d124 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10948 (p : Pattern) (guard : d1 p = 1) : d118 p ≤ (0 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d118, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d118, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d118, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1595 p hg
    simpa only [d118, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10949 (p : Pattern) (guard : d4147 p = 1) : d118 p ≤ (0 : Int) + d124 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10947 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10948 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10950 (p : Pattern) (guard : d0 p = 1) : d126 p ≤ (0 : Int) + d124 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10951 (p : Pattern) (guard : d4765 p = 1) : d1441 p ≤ (0 : Int) + d124 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10949 p hg
    simpa only [d4765, d1441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10950 p hg
    simpa only [d4765, d1441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10952 (p : Pattern) (guard : d0 p = 1) : d124 p ≤ (0 : Int) + d70 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10953 (p : Pattern) (guard : d4147 p = 1) : d126 p ≤ (0 : Int) + d70 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10952 p hg
    simpa only [d4147, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1287 p hg
    simpa only [d4147, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10954 (p : Pattern) (guard : d0 p = 1) : d128 p ≤ (0 : Int) + d70 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10955 (p : Pattern) (guard : d4765 p = 1) : d129 p ≤ (0 : Int) + d70 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10953 p hg
    simpa only [d4765, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10954 p hg
    simpa only [d4765, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10956 (p : Pattern) (guard : d4765 p = 1) : d1442 p ≤ (0 : Int) + d4871 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1442, d4871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10951 p hg
    simpa only [d1442, d4871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1442, d4871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10955 p hg
    simpa only [d1442, d4871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10957 (p : Pattern) (guard : d4765 p = 1) : d1443 p ≤ (0 : Int) + d4872 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1443, d4872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10946 p hg
    simpa only [d1443, d4872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1443, d4872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10956 p hg
    simpa only [d1443, d4872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10958 (p : Pattern) (guard : d0 p = 1) : d105 p ≤ (0 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10959 (p : Pattern) (guard : d4147 p = 1) : d133 p ≤ (0 : Int) + d132 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10958 p hg
    simpa only [d4147, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1434 p hg
    simpa only [d4147, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10960 (p : Pattern) (guard : d0 p = 1) : d1284 p ≤ (0 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10961 (p : Pattern) (guard : d4765 p = 1) : d1444 p ≤ (0 : Int) + d132 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10959 p hg
    simpa only [d4765, d1444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10960 p hg
    simpa only [d4765, d1444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10962 (p : Pattern) (guard : d1 p = 1) : d861 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1573 p hg
    simpa only [d861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1322 p hg
    simpa only [d861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10963 (p : Pattern) (guard : d4147 p = 1) : d862 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8230 p hg
    simpa only [d4147, d862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10962 p hg
    simpa only [d4147, d862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10964 (p : Pattern) (guard : d4765 p = 1) : d1051 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10963 p hg
    simpa only [d4765, d1051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4765, d1051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10965 (p : Pattern) (guard : d4765 p = 1) : d1445 p ≤ (0 : Int) + d4705 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1445, d4705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10961 p hg
    simpa only [d1445, d4705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1445, d4705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10964 p hg
    simpa only [d1445, d4705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10966 (p : Pattern) (guard : d0 p = 1) : d132 p ≤ (0 : Int) + d139 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10967 (p : Pattern) (guard : d1 p = 1) : d861 p ≤ (0 : Int) + d139 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d861, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d861, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d861, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1322 p hg
    simpa only [d861, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10968 (p : Pattern) (guard : d4147 p = 1) : d862 p ≤ (0 : Int) + d139 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10966 p hg
    simpa only [d4147, d862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10967 p hg
    simpa only [d4147, d862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10969 (p : Pattern) (guard : d0 p = 1) : d1290 p ≤ (0 : Int) + d139 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10970 (p : Pattern) (guard : d4765 p = 1) : d1446 p ≤ (0 : Int) + d139 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10968 p hg
    simpa only [d4765, d1446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10969 p hg
    simpa only [d4765, d1446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10971 (p : Pattern) (guard : d0 p = 1) : d139 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10972 (p : Pattern) (guard : d4147 p = 1) : d1053 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10971 p hg
    simpa only [d4147, d1053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1666 p hg
    simpa only [d4147, d1053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10973 (p : Pattern) (guard : d4765 p = 1) : d1054 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10972 p hg
    simpa only [d4765, d1054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4765, d1054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10974 (p : Pattern) (guard : d4765 p = 1) : d1447 p ≤ (0 : Int) + d4873 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1447, d4873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10970 p hg
    simpa only [d1447, d4873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1447, d4873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10973 p hg
    simpa only [d1447, d4873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10975 (p : Pattern) (guard : d4765 p = 1) : d1448 p ≤ (0 : Int) + d4874 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1448, d4874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10965 p hg
    simpa only [d1448, d4874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1448, d4874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10974 p hg
    simpa only [d1448, d4874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10976 (p : Pattern) (guard : d4765 p = 1) : d1449 p ≤ (0 : Int) + d4875 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1449, d4875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10957 p hg
    simpa only [d1449, d4875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1449, d4875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10975 p hg
    simpa only [d1449, d4875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10977 (p : Pattern) (guard : d1 p = 1) : d132 p ≤ (0 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d132, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10940 p hg
    simpa only [d132, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d132, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10941 p hg
    simpa only [d132, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10978 (p : Pattern) (guard : d4147 p = 1) : d133 p ≤ (0 : Int) + d60 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10937 p hg
    simpa only [d4147, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10977 p hg
    simpa only [d4147, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10979 (p : Pattern) (guard : d4765 p = 1) : d1450 p ≤ (0 : Int) + d60 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10978 p hg
    simpa only [d4765, d1450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10944 p hg
    simpa only [d4765, d1450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10980 (p : Pattern) (guard : d4765 p = 1) : d1451 p ≤ (0 : Int) + d4870 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1451, d4870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10936 p hg
    simpa only [d1451, d4870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1451, d4870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10979 p hg
    simpa only [d1451, d4870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10981 (p : Pattern) (guard : d4147 p = 1) : d132 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8230 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1596 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10982 (p : Pattern) (guard : d4765 p = 1) : d1061 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10981 p hg
    simpa only [d4765, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4765, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10983 (p : Pattern) (guard : d4765 p = 1) : d1062 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10982 p hg
    simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10892 p hg
    simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10984 (p : Pattern) (guard : d4765 p = 1) : d1452 p ≤ (0 : Int) + d4876 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1452, d4876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10980 p hg
    simpa only [d1452, d4876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1452, d4876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10983 p hg
    simpa only [d1452, d4876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10985 (p : Pattern) (guard : d0 p = 1) : d1289 p ≤ (0 : Int) + d132 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10986 (p : Pattern) (guard : d4765 p = 1) : d1453 p ≤ (0 : Int) + d132 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10959 p hg
    simpa only [d4765, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10985 p hg
    simpa only [d4765, d1453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10987 (p : Pattern) (guard : d4147 p = 1) : d873 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8230 p hg
    simpa only [d4147, d873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1323 p hg
    simpa only [d4147, d873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10988 (p : Pattern) (guard : d4765 p = 1) : d1064 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10987 p hg
    simpa only [d4765, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4765, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10989 (p : Pattern) (guard : d4765 p = 1) : d1454 p ≤ (0 : Int) + d4705 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1454, d4705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10986 p hg
    simpa only [d1454, d4705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1454, d4705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d1454, d4705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10990 (p : Pattern) (guard : d4765 p = 1) : d1066 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10892 p hg
    simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10991 (p : Pattern) (guard : d4765 p = 1) : d1455 p ≤ (0 : Int) + d4877 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1455, d4877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d1455, d4877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1455, d4877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d1455, d4877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10992 (p : Pattern) (guard : d4765 p = 1) : d1456 p ≤ (0 : Int) + d4878 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1456, d4878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10984 p hg
    simpa only [d1456, d4878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1456, d4878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10991 p hg
    simpa only [d1456, d4878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10993 (p : Pattern) (guard : d4765 p = 1) : d1457 p ≤ (0 : Int) + d4879 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1457, d4879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10976 p hg
    simpa only [d1457, d4879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1457, d4879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10992 p hg
    simpa only [d1457, d4879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10994 (p : Pattern) (guard : d0 p = 1) : d60 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10995 (p : Pattern) (guard : d4147 p = 1) : d112 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10994 p hg
    simpa only [d4147, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d4147, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10996 (p : Pattern) (guard : d4765 p = 1) : d159 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10995 p hg
    simpa only [d4765, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4765, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10997 (p : Pattern) (guard : d4765 p = 1) : d160 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10996 p hg
    simpa only [d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10892 p hg
    simpa only [d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10998 (p : Pattern) (guard : d4765 p = 1) : d161 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10997 p hg
    simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10892 p hg
    simpa only [d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10999 (p : Pattern) (guard : d4765 p = 1) : d162 p ≤ (0 : Int) + d12 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10998 p hg
    simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10892 p hg
    simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11000 (p : Pattern) (guard : d4765 p = 1) : d1458 p ≤ (0 : Int) + d4880 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1458, d4880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10992 p hg
    simpa only [d1458, d4880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1458, d4880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10999 p hg
    simpa only [d1458, d4880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11001 (p : Pattern) (guard : d4765 p = 1) : d1459 p ≤ (0 : Int) + d4881 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1459, d4881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d1459, d4881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1459, d4881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11000 p hg
    simpa only [d1459, d4881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11002 (p : Pattern) (guard : d4765 p = 1) : d1460 p ≤ (0 : Int) + d4705 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1460, d4705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10986 p hg
    simpa only [d1460, d4705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1460, d4705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10964 p hg
    simpa only [d1460, d4705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11003 (p : Pattern) (guard : d4765 p = 1) : d1461 p ≤ (0 : Int) + d4874 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1461, d4874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11002 p hg
    simpa only [d1461, d4874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1461, d4874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10974 p hg
    simpa only [d1461, d4874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11004 (p : Pattern) (guard : d4765 p = 1) : d1462 p ≤ (0 : Int) + d4875 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1462, d4875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10957 p hg
    simpa only [d1462, d4875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1462, d4875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d1462, d4875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11005 (p : Pattern) (guard : d4765 p = 1) : d1463 p ≤ (0 : Int) + d4879 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1463, d4879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11004 p hg
    simpa only [d1463, d4879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1463, d4879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10992 p hg
    simpa only [d1463, d4879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11006 (p : Pattern) (guard : d4765 p = 1) : d1464 p ≤ (0 : Int) + d4880 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1464, d4880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10992 p hg
    simpa only [d1464, d4880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1464, d4880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10892 p hg
    simpa only [d1464, d4880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11007 (p : Pattern) (guard : d4765 p = 1) : d1465 p ≤ (0 : Int) + d4881 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1465, d4881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11005 p hg
    simpa only [d1465, d4881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1465, d4881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11006 p hg
    simpa only [d1465, d4881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11008 (p : Pattern) (guard : d4765 p = 1) : d1466 p ≤ (0 : Int) + d4881 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11001 p hg
    simpa only [d1466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11007 p hg
    simpa only [d1466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11009 (p : Pattern) (guard : d4765 p = 1) : d1467 p ≤ (0 : Int) + d4882 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1467, d4882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10924 p hg
    simpa only [d1467, d4882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1467, d4882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11008 p hg
    simpa only [d1467, d4882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11010 (p : Pattern) (guard : d4765 p = 1) : d1468 p ≤ (0 : Int) + d4883 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1468, d4883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10933 p hg
    simpa only [d1468, d4883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1468, d4883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11009 p hg
    simpa only [d1468, d4883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11011 (p : Pattern) (guard : d4147 p = 1) : d53 p ≤ (0 : Int) + d53 p := by
  omega
theorem compare11012 (p : Pattern) (guard : d4765 p = 1) : d1469 p ≤ (0 : Int) + d53 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11011 p hg
    simpa only [d4765, d1469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10895 p hg
    simpa only [d4765, d1469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11013 (p : Pattern) (guard : d4765 p = 1) : d1470 p ≤ (0 : Int) + d4857 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1470, d4857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11012 p hg
    simpa only [d1470, d4857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1470, d4857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10898 p hg
    simpa only [d1470, d4857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11014 (p : Pattern) (guard : d4147 p = 1) : d20 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3640 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1527 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11015 (p : Pattern) (guard : d4765 p = 1) : d1100 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11014 p hg
    simpa only [d4765, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4765, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11016 (p : Pattern) (guard : d4765 p = 1) : d1101 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11015 p hg
    simpa only [d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10892 p hg
    simpa only [d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11017 (p : Pattern) (guard : d4765 p = 1) : d1471 p ≤ (0 : Int) + d4862 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1471, d4862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11013 p hg
    simpa only [d1471, d4862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1471, d4862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11016 p hg
    simpa only [d1471, d4862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11018 (p : Pattern) (guard : d4765 p = 1) : d1472 p ≤ (0 : Int) + d4863 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1472, d4863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10894 p hg
    simpa only [d1472, d4863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1472, d4863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11017 p hg
    simpa only [d1472, d4863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11019 (p : Pattern) (guard : d4765 p = 1) : d1473 p ≤ (0 : Int) + d4864 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1473, d4864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10920 p hg
    simpa only [d1473, d4864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1473, d4864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11018 p hg
    simpa only [d1473, d4864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11020 (p : Pattern) (guard : d4765 p = 1) : d1474 p ≤ (0 : Int) + d4867 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1474, d4867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11018 p hg
    simpa only [d1474, d4867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1474, d4867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10892 p hg
    simpa only [d1474, d4867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11021 (p : Pattern) (guard : d4765 p = 1) : d1475 p ≤ (0 : Int) + d4868 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1475, d4868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11019 p hg
    simpa only [d1475, d4868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1475, d4868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11020 p hg
    simpa only [d1475, d4868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11022 (p : Pattern) (guard : d4765 p = 1) : d1476 p ≤ (0 : Int) + d4869 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1476, d4869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10931 p hg
    simpa only [d1476, d4869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1476, d4869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11021 p hg
    simpa only [d1476, d4869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11023 (p : Pattern) (guard : d4765 p = 1) : d1477 p ≤ (0 : Int) + d4869 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10924 p hg
    simpa only [d1477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11022 p hg
    simpa only [d1477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11024 (p : Pattern) (guard : d4765 p = 1) : d1478 p ≤ (0 : Int) + d4881 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1478, d4881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11005 p hg
    simpa only [d1478, d4881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1478, d4881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11000 p hg
    simpa only [d1478, d4881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11025 (p : Pattern) (guard : d1 p = 1) : d268 p ≤ (0 : Int) + d58 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1585 p hg
    simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10940 p hg
    simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11026 (p : Pattern) (guard : d1 p = 1) : d269 p ≤ (0 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d269, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11025 p hg
    simpa only [d269, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d269, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10941 p hg
    simpa only [d269, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11027 (p : Pattern) (guard : d4147 p = 1) : d291 p ≤ (0 : Int) + d60 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10937 p hg
    simpa only [d4147, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11026 p hg
    simpa only [d4147, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11028 (p : Pattern) (guard : d4765 p = 1) : d1479 p ≤ (0 : Int) + d60 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11027 p hg
    simpa only [d4765, d1479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10944 p hg
    simpa only [d4765, d1479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11029 (p : Pattern) (guard : d4765 p = 1) : d1480 p ≤ (0 : Int) + d4870 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1480, d4870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10936 p hg
    simpa only [d1480, d4870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1480, d4870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11028 p hg
    simpa only [d1480, d4870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11030 (p : Pattern) (guard : d0 p = 1) : d269 p ≤ (0 : Int) + d272 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11031 (p : Pattern) (guard : d4147 p = 1) : d269 p ≤ (0 : Int) + d272 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11030 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2096 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11032 (p : Pattern) (guard : d0 p = 1) : d275 p ≤ (0 : Int) + d272 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11033 (p : Pattern) (guard : d4765 p = 1) : d1481 p ≤ (0 : Int) + d272 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d4765, d1481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d4765, d1481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11034 (p : Pattern) (guard : d0 p = 1) : d272 p ≤ (0 : Int) + d277 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11035 (p : Pattern) (guard : d1 p = 1) : d273 p ≤ (0 : Int) + d59 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d273, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1260 p hg
    simpa only [d273, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d273, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1282 p hg
    simpa only [d273, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11036 (p : Pattern) (guard : d1 p = 1) : d274 p ≤ (0 : Int) + d277 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d274, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11035 p hg
    simpa only [d274, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d274, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d274, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11037 (p : Pattern) (guard : d4147 p = 1) : d275 p ≤ (0 : Int) + d277 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11034 p hg
    simpa only [d4147, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d4147, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11038 (p : Pattern) (guard : d0 p = 1) : d278 p ≤ (0 : Int) + d277 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11039 (p : Pattern) (guard : d4765 p = 1) : d279 p ≤ (0 : Int) + d277 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11037 p hg
    simpa only [d4765, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11038 p hg
    simpa only [d4765, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11040 (p : Pattern) (guard : d4765 p = 1) : d1482 p ≤ (0 : Int) + d4884 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1482, d4884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11033 p hg
    simpa only [d1482, d4884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1482, d4884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11039 p hg
    simpa only [d1482, d4884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11041 (p : Pattern) (guard : d4765 p = 1) : d1483 p ≤ (0 : Int) + d4885 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1483, d4885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11029 p hg
    simpa only [d1483, d4885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1483, d4885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11040 p hg
    simpa only [d1483, d4885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11042 (p : Pattern) (guard : d1 p = 1) : d282 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1573 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1321 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11043 (p : Pattern) (guard : d1 p = 1) : d298 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11042 p hg
    simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1322 p hg
    simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11044 (p : Pattern) (guard : d4147 p = 1) : d925 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8230 p hg
    simpa only [d4147, d925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11043 p hg
    simpa only [d4147, d925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11045 (p : Pattern) (guard : d4765 p = 1) : d1124 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11044 p hg
    simpa only [d4765, d1124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4765, d1124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11046 (p : Pattern) (guard : d4765 p = 1) : d1484 p ≤ (0 : Int) + d4705 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1484, d4705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10986 p hg
    simpa only [d1484, d4705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1484, d4705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11045 p hg
    simpa only [d1484, d4705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11047 (p : Pattern) (guard : d0 p = 1) : d132 p ≤ (0 : Int) + d283 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11048 (p : Pattern) (guard : d4147 p = 1) : d925 p ≤ (0 : Int) + d283 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11047 p hg
    simpa only [d4147, d925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2107 p hg
    simpa only [d4147, d925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11049 (p : Pattern) (guard : d0 p = 1) : d1375 p ≤ (0 : Int) + d283 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11050 (p : Pattern) (guard : d4765 p = 1) : d1485 p ≤ (0 : Int) + d283 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11048 p hg
    simpa only [d4765, d1485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11049 p hg
    simpa only [d4765, d1485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11051 (p : Pattern) (guard : d0 p = 1) : d283 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11052 (p : Pattern) (guard : d1 p = 1) : d1126 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1282 p hg
    simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare868 p hg
    simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11053 (p : Pattern) (guard : d1 p = 1) : d1127 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11052 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11054 (p : Pattern) (guard : d4147 p = 1) : d1128 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11051 p hg
    simpa only [d4147, d1128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11053 p hg
    simpa only [d4147, d1128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11055 (p : Pattern) (guard : d4765 p = 1) : d1129 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4147 p = 1 := by simpa only [d4765, d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11054 p hg
    simpa only [d4765, d1129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4765, d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4765, d1129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11056 (p : Pattern) (guard : d4765 p = 1) : d1486 p ≤ (0 : Int) + d4886 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1486, d4886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11050 p hg
    simpa only [d1486, d4886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1486, d4886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11055 p hg
    simpa only [d1486, d4886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11057 (p : Pattern) (guard : d4765 p = 1) : d1487 p ≤ (0 : Int) + d4887 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1487, d4887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d1487, d4887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1487, d4887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11056 p hg
    simpa only [d1487, d4887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11058 (p : Pattern) (guard : d4765 p = 1) : d1488 p ≤ (0 : Int) + d4888 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4765 p = 1 := by simpa only [d1488, d4888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11041 p hg
    simpa only [d1488, d4888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4765 p = 1 := by simpa only [d1488, d4888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11057 p hg
    simpa only [d1488, d4888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11059 (p : Pattern) (guard : d4147 p = 1) : d105 p ≤ (0 : Int) + d269 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9301 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1364 p hg
    simpa only [d4147, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
