/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons034
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare4900 (p : Pattern) (guard : d857 p = 1) : d59 p ≤ (0 : Int) + d403 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d59, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare229 p hg
    simpa only [d857, d59, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d59, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4899 p hg
    simpa only [d857, d59, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4901 (p : Pattern) (guard : d857 p = 1) : d60 p ≤ (0 : Int) + d404 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d60, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4894 p hg
    simpa only [d60, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d60, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4900 p hg
    simpa only [d60, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4902 (p : Pattern) (guard : d0 p = 1) : d61 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4903 (p : Pattern) (guard : d857 p = 1) : d62 p ≤ (0 : Int) + d405 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d62, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare236 p hg
    simpa only [d857, d62, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d62, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4902 p hg
    simpa only [d857, d62, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4904 (p : Pattern) (guard : d857 p = 1) : d63 p ≤ (0 : Int) + d406 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d63, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4903 p hg
    simpa only [d63, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d63, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4896 p hg
    simpa only [d63, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4905 (p : Pattern) (guard : d857 p = 1) : d64 p ≤ (0 : Int) + d407 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d64, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4901 p hg
    simpa only [d64, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d64, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4904 p hg
    simpa only [d64, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4906 (p : Pattern) (guard : d857 p = 1) : d65 p ≤ (0 : Int) + d408 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d65, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4898 p hg
    simpa only [d65, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d65, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4905 p hg
    simpa only [d65, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4907 (p : Pattern) (guard : d857 p = 1) : d66 p ≤ (0 : Int) + d408 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4892 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4906 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4908 (p : Pattern) (guard : d857 p = 1) : d67 p ≤ (0 : Int) + d409 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d67, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1447 p hg
    simpa only [d67, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d67, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4907 p hg
    simpa only [d67, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4909 (p : Pattern) (guard : d857 p = 1) : d79 p ≤ (0 : Int) + d418 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d79, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4885 p hg
    simpa only [d79, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d79, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1461 p hg
    simpa only [d79, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4910 (p : Pattern) (guard : d857 p = 1) : d80 p ≤ (0 : Int) + d419 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d80, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4886 p hg
    simpa only [d80, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d80, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4909 p hg
    simpa only [d80, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4911 (p : Pattern) (guard : d857 p = 1) : d81 p ≤ (0 : Int) + d418 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d81, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4897 p hg
    simpa only [d81, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d81, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1461 p hg
    simpa only [d81, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4912 (p : Pattern) (guard : d857 p = 1) : d82 p ≤ (0 : Int) + d419 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d82, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4898 p hg
    simpa only [d82, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d82, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4911 p hg
    simpa only [d82, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4913 (p : Pattern) (guard : d857 p = 1) : d83 p ≤ (0 : Int) + d419 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4910 p hg
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4912 p hg
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4914 (p : Pattern) (guard : d857 p = 1) : d84 p ≤ (0 : Int) + d420 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d84, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1464 p hg
    simpa only [d84, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d84, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4913 p hg
    simpa only [d84, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4915 (p : Pattern) (guard : d857 p = 1) : d85 p ≤ (0 : Int) + d421 p := by
  cases selected : p 106 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d85, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4908 p hg
    simpa only [d85, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d85, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4914 p hg
    simpa only [d85, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4916 (p : Pattern) (guard : d857 p = 1) : d86 p ≤ (0 : Int) + d389 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d86, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d857, d86, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d86, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d857, d86, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4917 (p : Pattern) (guard : d857 p = 1) : d87 p ≤ (0 : Int) + d390 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d87, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare211 p hg
    simpa only [d857, d87, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d87, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4895 p hg
    simpa only [d857, d87, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4918 (p : Pattern) (guard : d857 p = 1) : d88 p ≤ (0 : Int) + d391 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d88, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4916 p hg
    simpa only [d88, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d88, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4917 p hg
    simpa only [d88, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4919 (p : Pattern) (guard : d857 p = 1) : d89 p ≤ (0 : Int) + d392 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d89, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4916 p hg
    simpa only [d89, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d89, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4918 p hg
    simpa only [d89, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4920 (p : Pattern) (guard : d857 p = 1) : d90 p ≤ (0 : Int) + d393 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d90, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare221 p hg
    simpa only [d857, d90, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d90, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4899 p hg
    simpa only [d857, d90, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4921 (p : Pattern) (guard : d857 p = 1) : d91 p ≤ (0 : Int) + d394 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d91, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4916 p hg
    simpa only [d91, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d91, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4920 p hg
    simpa only [d91, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4922 (p : Pattern) (guard : d857 p = 1) : d92 p ≤ (0 : Int) + d395 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d92, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d857, d92, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d92, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4902 p hg
    simpa only [d857, d92, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4923 (p : Pattern) (guard : d857 p = 1) : d93 p ≤ (0 : Int) + d396 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d93, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4922 p hg
    simpa only [d93, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d93, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4917 p hg
    simpa only [d93, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4924 (p : Pattern) (guard : d857 p = 1) : d94 p ≤ (0 : Int) + d397 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d94, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4921 p hg
    simpa only [d94, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d94, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4923 p hg
    simpa only [d94, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4925 (p : Pattern) (guard : d857 p = 1) : d95 p ≤ (0 : Int) + d398 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d95, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4919 p hg
    simpa only [d95, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d95, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4924 p hg
    simpa only [d95, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4926 (p : Pattern) (guard : d857 p = 1) : d96 p ≤ (0 : Int) + d398 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1447 p hg
    simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4925 p hg
    simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4927 (p : Pattern) (guard : d857 p = 1) : d98 p ≤ (0 : Int) + d422 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d98, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1816 p hg
    simpa only [d857, d98, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d98, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare919 p hg
    simpa only [d857, d98, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4928 (p : Pattern) (guard : d857 p = 1) : d99 p ≤ (0 : Int) + d423 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d99, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4927 p hg
    simpa only [d99, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d99, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1454 p hg
    simpa only [d99, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4929 (p : Pattern) (guard : d857 p = 1) : d100 p ≤ (0 : Int) + d424 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d100, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4927 p hg
    simpa only [d100, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d100, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4928 p hg
    simpa only [d100, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4930 (p : Pattern) (guard : d857 p = 1) : d101 p ≤ (0 : Int) + d425 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d101, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4928 p hg
    simpa only [d101, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d101, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1455 p hg
    simpa only [d101, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4931 (p : Pattern) (guard : d857 p = 1) : d102 p ≤ (0 : Int) + d426 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d102, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4929 p hg
    simpa only [d102, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d102, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4930 p hg
    simpa only [d102, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4932 (p : Pattern) (guard : d857 p = 1) : d103 p ≤ (0 : Int) + d427 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d103, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4926 p hg
    simpa only [d103, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d103, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4931 p hg
    simpa only [d103, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4933 (p : Pattern) (guard : d857 p = 1) : d104 p ≤ (0 : Int) + d415 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d104, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4918 p hg
    simpa only [d104, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d104, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1461 p hg
    simpa only [d104, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4934 (p : Pattern) (guard : d857 p = 1) : d105 p ≤ (0 : Int) + d416 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d105, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4919 p hg
    simpa only [d105, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d105, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4933 p hg
    simpa only [d105, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4935 (p : Pattern) (guard : d857 p = 1) : d106 p ≤ (0 : Int) + d416 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1463 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4934 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4936 (p : Pattern) (guard : d857 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare4937 (p : Pattern) (guard : d857 p = 1) : d107 p ≤ (0 : Int) + d428 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d107, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4928 p hg
    simpa only [d107, d428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d107, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4936 p hg
    simpa only [d107, d428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4938 (p : Pattern) (guard : d857 p = 1) : d108 p ≤ (0 : Int) + d429 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d108, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4929 p hg
    simpa only [d108, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d108, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4937 p hg
    simpa only [d108, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4939 (p : Pattern) (guard : d857 p = 1) : d97 p ≤ (0 : Int) + d430 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare831 p hg
    simpa only [d857, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare919 p hg
    simpa only [d857, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4940 (p : Pattern) (guard : d857 p = 1) : d109 p ≤ (0 : Int) + d431 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d109, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4939 p hg
    simpa only [d109, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d109, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1460 p hg
    simpa only [d109, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4941 (p : Pattern) (guard : d857 p = 1) : d110 p ≤ (0 : Int) + d432 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d110, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4939 p hg
    simpa only [d110, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d110, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4940 p hg
    simpa only [d110, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4942 (p : Pattern) (guard : d857 p = 1) : d111 p ≤ (0 : Int) + d433 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d111, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4940 p hg
    simpa only [d111, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d111, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4936 p hg
    simpa only [d111, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4943 (p : Pattern) (guard : d857 p = 1) : d112 p ≤ (0 : Int) + d434 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d112, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4941 p hg
    simpa only [d112, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d112, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4942 p hg
    simpa only [d112, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4944 (p : Pattern) (guard : d857 p = 1) : d113 p ≤ (0 : Int) + d435 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d113, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4938 p hg
    simpa only [d113, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d113, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4943 p hg
    simpa only [d113, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4945 (p : Pattern) (guard : d857 p = 1) : d114 p ≤ (0 : Int) + d436 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d114, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4935 p hg
    simpa only [d114, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d114, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4944 p hg
    simpa only [d114, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4946 (p : Pattern) (guard : d857 p = 1) : d115 p ≤ (0 : Int) + d437 p := by
  cases selected : p 106 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d115, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4932 p hg
    simpa only [d115, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d115, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4945 p hg
    simpa only [d115, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4947 (p : Pattern) (guard : d857 p = 1) : d116 p ≤ (0 : Int) + d438 p := by
  cases selected : p 86 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d116, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4915 p hg
    simpa only [d116, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d116, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4946 p hg
    simpa only [d116, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4948 (p : Pattern) (guard : d857 p = 1) : d117 p ≤ (0 : Int) + d439 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d117, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1463 p hg
    simpa only [d117, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d117, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4913 p hg
    simpa only [d117, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4949 (p : Pattern) (guard : d857 p = 1) : d118 p ≤ (0 : Int) + d440 p := by
  cases selected : p 106 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d118, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4908 p hg
    simpa only [d118, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d118, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4948 p hg
    simpa only [d118, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4950 (p : Pattern) (guard : d857 p = 1) : d120 p ≤ (0 : Int) + d441 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d857, d120, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1494 p hg
    simpa only [d857, d120, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d857, d120, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4899 p hg
    simpa only [d857, d120, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4951 (p : Pattern) (guard : d857 p = 1) : d121 p ≤ (0 : Int) + d442 p := by
  cases selected : p 134 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d121, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4916 p hg
    simpa only [d121, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d121, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4950 p hg
    simpa only [d121, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4952 (p : Pattern) (guard : d857 p = 1) : d122 p ≤ (0 : Int) + d443 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d122, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4951 p hg
    simpa only [d122, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d122, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4923 p hg
    simpa only [d122, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4953 (p : Pattern) (guard : d857 p = 1) : d123 p ≤ (0 : Int) + d444 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d123, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4919 p hg
    simpa only [d123, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d123, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4952 p hg
    simpa only [d123, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4954 (p : Pattern) (guard : d857 p = 1) : d124 p ≤ (0 : Int) + d445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d124, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1447 p hg
    simpa only [d124, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d124, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4953 p hg
    simpa only [d124, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4955 (p : Pattern) (guard : d857 p = 1) : d125 p ≤ (0 : Int) + d446 p := by
  cases selected : p 133 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d125, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4940 p hg
    simpa only [d125, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d125, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1461 p hg
    simpa only [d125, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4956 (p : Pattern) (guard : d857 p = 1) : d126 p ≤ (0 : Int) + d447 p := by
  cases selected : p 132 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d126, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4941 p hg
    simpa only [d126, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d126, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4955 p hg
    simpa only [d126, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4957 (p : Pattern) (guard : d857 p = 1) : d127 p ≤ (0 : Int) + d448 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d127, d448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4931 p hg
    simpa only [d127, d448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d127, d448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4956 p hg
    simpa only [d127, d448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4958 (p : Pattern) (guard : d857 p = 1) : d128 p ≤ (0 : Int) + d449 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d128, d449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4954 p hg
    simpa only [d128, d449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d128, d449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4957 p hg
    simpa only [d128, d449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4959 (p : Pattern) (guard : d857 p = 1) : d129 p ≤ (0 : Int) + d450 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d129, d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1463 p hg
    simpa only [d129, d450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d129, d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4912 p hg
    simpa only [d129, d450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4960 (p : Pattern) (guard : d857 p = 1) : d130 p ≤ (0 : Int) + d451 p := by
  cases selected : p 113 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d130, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4943 p hg
    simpa only [d130, d451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d130, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4936 p hg
    simpa only [d130, d451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4961 (p : Pattern) (guard : d857 p = 1) : d131 p ≤ (0 : Int) + d452 p := by
  cases selected : p 112 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d131, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4959 p hg
    simpa only [d131, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d131, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4960 p hg
    simpa only [d131, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4962 (p : Pattern) (guard : d857 p = 1) : d132 p ≤ (0 : Int) + d453 p := by
  cases selected : p 106 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d132, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4958 p hg
    simpa only [d132, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d132, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4961 p hg
    simpa only [d132, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4963 (p : Pattern) (guard : d857 p = 1) : d133 p ≤ (0 : Int) + d454 p := by
  cases selected : p 86 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d133, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4949 p hg
    simpa only [d133, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d133, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4962 p hg
    simpa only [d133, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4964 (p : Pattern) (guard : d857 p = 1) : d134 p ≤ (0 : Int) + d455 p := by
  cases selected : p 80 with
  | false =>
    have hg : d857 p = 1 := by simpa only [d134, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4947 p hg
    simpa only [d134, d455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d857 p = 1 := by simpa only [d134, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4963 p hg
    simpa only [d134, d455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4965 (p : Pattern) (guard : d0 p = 1) : d8 p ≤ (3 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4966 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (3 : Int) + d8 p := by
  omega
theorem compare4967 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (3 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4968 (p : Pattern) (guard : d1088 p = 1) : d15 p ≤ (3 : Int) + d8 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4966 p hg
    simpa only [d1088, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4967 p hg
    simpa only [d1088, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4969 (p : Pattern) (guard : d1365 p = 1) : d16 p ≤ (3 : Int) + d8 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4965 p hg
    simpa only [d1365, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4968 p hg
    simpa only [d1365, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4970 (p : Pattern) (guard : d0 p = 1) : d20 p ≤ (3 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4971 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (3 : Int) + d20 p := by
  omega
theorem compare4972 (p : Pattern) (guard : d0 p = 1) : d24 p ≤ (3 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4973 (p : Pattern) (guard : d1088 p = 1) : d25 p ≤ (3 : Int) + d20 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4971 p hg
    simpa only [d1088, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4972 p hg
    simpa only [d1088, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4974 (p : Pattern) (guard : d1365 p = 1) : d26 p ≤ (3 : Int) + d20 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4970 p hg
    simpa only [d1365, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4973 p hg
    simpa only [d1365, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4975 (p : Pattern) (guard : d1365 p = 1) : d27 p ≤ (3 : Int) + d1097 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d27, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4969 p hg
    simpa only [d27, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d27, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4974 p hg
    simpa only [d27, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4976 (p : Pattern) (guard : d1365 p = 1) : d28 p ≤ (3 : Int) + d1098 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d28, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4969 p hg
    simpa only [d28, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d28, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4975 p hg
    simpa only [d28, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4977 (p : Pattern) (guard : d0 p = 1) : d33 p ≤ (3 : Int) + d33 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4978 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (3 : Int) + d33 p := by
  omega
theorem compare4979 (p : Pattern) (guard : d0 p = 1) : d24 p ≤ (3 : Int) + d33 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4980 (p : Pattern) (guard : d1088 p = 1) : d34 p ≤ (3 : Int) + d33 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4978 p hg
    simpa only [d1088, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4979 p hg
    simpa only [d1088, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4981 (p : Pattern) (guard : d1365 p = 1) : d35 p ≤ (3 : Int) + d33 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4977 p hg
    simpa only [d1365, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4980 p hg
    simpa only [d1365, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4982 (p : Pattern) (guard : d1365 p = 1) : d36 p ≤ (3 : Int) + d1099 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d36, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4969 p hg
    simpa only [d36, d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d36, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4981 p hg
    simpa only [d36, d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4983 (p : Pattern) (guard : d0 p = 1) : d38 p ≤ (3 : Int) + d38 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4984 (p : Pattern) (guard : d1 p = 1) : d38 p ≤ (3 : Int) + d38 p := by
  omega
theorem compare4985 (p : Pattern) (guard : d0 p = 1) : d40 p ≤ (3 : Int) + d38 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4986 (p : Pattern) (guard : d1088 p = 1) : d41 p ≤ (3 : Int) + d38 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4984 p hg
    simpa only [d1088, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4985 p hg
    simpa only [d1088, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4987 (p : Pattern) (guard : d1365 p = 1) : d42 p ≤ (3 : Int) + d38 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4983 p hg
    simpa only [d1365, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4986 p hg
    simpa only [d1365, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4988 (p : Pattern) (guard : d1365 p = 1) : d43 p ≤ (3 : Int) + d1100 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d43, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4987 p hg
    simpa only [d43, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d43, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4974 p hg
    simpa only [d43, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4989 (p : Pattern) (guard : d1365 p = 1) : d44 p ≤ (3 : Int) + d1101 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d44, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4982 p hg
    simpa only [d44, d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d44, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4988 p hg
    simpa only [d44, d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4990 (p : Pattern) (guard : d1365 p = 1) : d45 p ≤ (3 : Int) + d1102 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d45, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4976 p hg
    simpa only [d45, d1102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d45, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4989 p hg
    simpa only [d45, d1102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4991 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (3 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4992 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (3 : Int) + d1 p := by
  change (0 : Int) ≤ (3 : Int) + 1
  decide
theorem compare4993 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (3 : Int) + d2 p := by
  omega
theorem compare4994 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (3 : Int) + d9 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4992 p hg
    simpa only [d3, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4993 p hg
    simpa only [d3, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4995 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (3 : Int) + d10 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4992 p hg
    simpa only [d4, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4994 p hg
    simpa only [d4, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4996 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (3 : Int) + d11 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4992 p hg
    simpa only [d5, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4993 p hg
    simpa only [d5, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4997 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (3 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d6, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4995 p hg
    simpa only [d6, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d6, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4996 p hg
    simpa only [d6, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4998 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (3 : Int) + d13 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d7, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4995 p hg
    simpa only [d7, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d7, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4993 p hg
    simpa only [d7, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4999 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (3 : Int) + d14 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4997 p hg
    simpa only [d8, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d8, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4998 p hg
    simpa only [d8, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5000 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (3 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5001 (p : Pattern) (guard : d1088 p = 1) : d15 p ≤ (3 : Int) + d14 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4999 p hg
    simpa only [d1088, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5000 p hg
    simpa only [d1088, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5002 (p : Pattern) (guard : d1365 p = 1) : d15 p ≤ (3 : Int) + d14 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4991 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5001 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5003 (p : Pattern) (guard : d0 p = 1) : d25 p ≤ (3 : Int) + d24 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5004 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (3 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4994 p hg
    simpa only [d17, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4993 p hg
    simpa only [d17, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5005 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (3 : Int) + d22 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4995 p hg
    simpa only [d18, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5004 p hg
    simpa only [d18, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5006 (p : Pattern) (guard : d1 p = 1) : d19 p ≤ (3 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5004 p hg
    simpa only [d19, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4993 p hg
    simpa only [d19, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5007 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (3 : Int) + d24 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5005 p hg
    simpa only [d20, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5006 p hg
    simpa only [d20, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5008 (p : Pattern) (guard : d0 p = 1) : d24 p ≤ (3 : Int) + d24 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5009 (p : Pattern) (guard : d1088 p = 1) : d25 p ≤ (3 : Int) + d24 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5007 p hg
    simpa only [d1088, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5008 p hg
    simpa only [d1088, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5010 (p : Pattern) (guard : d1365 p = 1) : d25 p ≤ (3 : Int) + d24 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5003 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5009 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5011 (p : Pattern) (guard : d1365 p = 1) : d46 p ≤ (3 : Int) + d1107 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d46, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5002 p hg
    simpa only [d46, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d46, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5010 p hg
    simpa only [d46, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5012 (p : Pattern) (guard : d1365 p = 1) : d47 p ≤ (3 : Int) + d1108 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d47, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5002 p hg
    simpa only [d47, d1108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d47, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5011 p hg
    simpa only [d47, d1108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5013 (p : Pattern) (guard : d0 p = 1) : d34 p ≤ (3 : Int) + d24 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5014 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (3 : Int) + d2 p := by
  change (1 : Int) ≤ (3 : Int) + 2
  decide
theorem compare5015 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (3 : Int) + d9 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d29, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4992 p hg
    simpa only [d29, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5014 p hg
    simpa only [d29, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5016 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (3 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5015 p hg
    simpa only [d30, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4993 p hg
    simpa only [d30, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5017 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (3 : Int) + d22 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4995 p hg
    simpa only [d31, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5016 p hg
    simpa only [d31, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5018 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (3 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5016 p hg
    simpa only [d32, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4993 p hg
    simpa only [d32, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5019 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (3 : Int) + d24 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d33, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5017 p hg
    simpa only [d33, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d33, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5018 p hg
    simpa only [d33, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5020 (p : Pattern) (guard : d1088 p = 1) : d34 p ≤ (3 : Int) + d24 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5019 p hg
    simpa only [d1088, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5008 p hg
    simpa only [d1088, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5021 (p : Pattern) (guard : d1365 p = 1) : d34 p ≤ (3 : Int) + d24 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5013 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5020 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5022 (p : Pattern) (guard : d1365 p = 1) : d48 p ≤ (3 : Int) + d1107 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d48, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5002 p hg
    simpa only [d48, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d48, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5021 p hg
    simpa only [d48, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5023 (p : Pattern) (guard : d0 p = 1) : d41 p ≤ (3 : Int) + d40 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5024 (p : Pattern) (guard : d1 p = 1) : d37 p ≤ (3 : Int) + d39 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d37, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4996 p hg
    simpa only [d37, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d37, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4993 p hg
    simpa only [d37, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5025 (p : Pattern) (guard : d1 p = 1) : d38 p ≤ (3 : Int) + d40 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d38, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4997 p hg
    simpa only [d38, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d38, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5024 p hg
    simpa only [d38, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5026 (p : Pattern) (guard : d0 p = 1) : d40 p ≤ (3 : Int) + d40 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5027 (p : Pattern) (guard : d1088 p = 1) : d41 p ≤ (3 : Int) + d40 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5025 p hg
    simpa only [d1088, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5026 p hg
    simpa only [d1088, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5028 (p : Pattern) (guard : d1365 p = 1) : d41 p ≤ (3 : Int) + d40 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5023 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5027 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5029 (p : Pattern) (guard : d1365 p = 1) : d49 p ≤ (3 : Int) + d1103 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d49, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5028 p hg
    simpa only [d49, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d49, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5010 p hg
    simpa only [d49, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5030 (p : Pattern) (guard : d1365 p = 1) : d50 p ≤ (3 : Int) + d1109 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d50, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5022 p hg
    simpa only [d50, d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d50, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5029 p hg
    simpa only [d50, d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5031 (p : Pattern) (guard : d1365 p = 1) : d51 p ≤ (3 : Int) + d1110 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d51, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5012 p hg
    simpa only [d51, d1110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d51, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5030 p hg
    simpa only [d51, d1110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5032 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (3 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5033 (p : Pattern) (guard : d1088 p = 1) : d52 p ≤ (3 : Int) + d14 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4999 p hg
    simpa only [d1088, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5032 p hg
    simpa only [d1088, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5034 (p : Pattern) (guard : d1365 p = 1) : d53 p ≤ (3 : Int) + d14 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4991 p hg
    simpa only [d1365, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5033 p hg
    simpa only [d1365, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5035 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (3 : Int) + d24 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5036 (p : Pattern) (guard : d1088 p = 1) : d54 p ≤ (3 : Int) + d24 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5007 p hg
    simpa only [d1088, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5035 p hg
    simpa only [d1088, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5037 (p : Pattern) (guard : d1365 p = 1) : d55 p ≤ (3 : Int) + d24 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5003 p hg
    simpa only [d1365, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5036 p hg
    simpa only [d1365, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5038 (p : Pattern) (guard : d1365 p = 1) : d56 p ≤ (3 : Int) + d1107 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d56, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5034 p hg
    simpa only [d56, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d56, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5037 p hg
    simpa only [d56, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5039 (p : Pattern) (guard : d1365 p = 1) : d57 p ≤ (3 : Int) + d1108 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d57, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5034 p hg
    simpa only [d57, d1108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d57, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5038 p hg
    simpa only [d57, d1108, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
