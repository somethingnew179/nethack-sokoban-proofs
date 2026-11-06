/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons041
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare5880 (p : Pattern) (guard : d1088 p = 1) : d520 p ≤ (0 : Int) + d122 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d520, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5879 p hg
    simpa only [d520, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d520, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5848 p hg
    simpa only [d520, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5881 (p : Pattern) (guard : d1088 p = 1) : d529 p ≤ (0 : Int) + d123 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d529, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5856 p hg
    simpa only [d529, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d529, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5880 p hg
    simpa only [d529, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5882 (p : Pattern) (guard : d1088 p = 1) : d530 p ≤ (0 : Int) + d124 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d530, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5795 p hg
    simpa only [d530, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d530, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5881 p hg
    simpa only [d530, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5883 (p : Pattern) (guard : d1088 p = 1) : d126 p ≤ (0 : Int) + d126 p := by
  omega
theorem compare5884 (p : Pattern) (guard : d1088 p = 1) : d531 p ≤ (0 : Int) + d127 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d531, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5799 p hg
    simpa only [d531, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d531, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5883 p hg
    simpa only [d531, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5885 (p : Pattern) (guard : d1088 p = 1) : d532 p ≤ (0 : Int) + d128 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d532, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5882 p hg
    simpa only [d532, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d532, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5884 p hg
    simpa only [d532, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5886 (p : Pattern) (guard : d1088 p = 1) : d533 p ≤ (0 : Int) + d129 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d533, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5806 p hg
    simpa only [d533, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d533, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5873 p hg
    simpa only [d533, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5887 (p : Pattern) (guard : d1088 p = 1) : d130 p ≤ (0 : Int) + d130 p := by
  omega
theorem compare5888 (p : Pattern) (guard : d1088 p = 1) : d534 p ≤ (0 : Int) + d131 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d534, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5886 p hg
    simpa only [d534, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d534, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5887 p hg
    simpa only [d534, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5889 (p : Pattern) (guard : d1088 p = 1) : d535 p ≤ (0 : Int) + d132 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d535, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5885 p hg
    simpa only [d535, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d535, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5888 p hg
    simpa only [d535, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5890 (p : Pattern) (guard : d1088 p = 1) : d536 p ≤ (0 : Int) + d133 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d536, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5876 p hg
    simpa only [d536, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d536, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5889 p hg
    simpa only [d536, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5891 (p : Pattern) (guard : d1088 p = 1) : d537 p ≤ (0 : Int) + d134 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d537, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5864 p hg
    simpa only [d537, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d537, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5890 p hg
    simpa only [d537, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5892 (p : Pattern) (guard : d1092 p = 1) : d457 p ≤ (0 : Int) + d389 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d457, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5684 p hg
    simpa only [d1092, d457, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d457, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d1092, d457, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5893 (p : Pattern) (guard : d1092 p = 1) : d52 p ≤ (0 : Int) + d389 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5689 p hg
    simpa only [d1092, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d1092, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5894 (p : Pattern) (guard : d1092 p = 1) : d458 p ≤ (0 : Int) + d389 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5892 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5893 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5895 (p : Pattern) (guard : d1092 p = 1) : d460 p ≤ (0 : Int) + d389 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d460, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5693 p hg
    simpa only [d1092, d460, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d460, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d1092, d460, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5896 (p : Pattern) (guard : d1092 p = 1) : d54 p ≤ (0 : Int) + d390 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5696 p hg
    simpa only [d1092, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4895 p hg
    simpa only [d1092, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5897 (p : Pattern) (guard : d1092 p = 1) : d461 p ≤ (0 : Int) + d391 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d461, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5895 p hg
    simpa only [d461, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d461, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5896 p hg
    simpa only [d461, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5898 (p : Pattern) (guard : d1092 p = 1) : d462 p ≤ (0 : Int) + d392 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d462, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5894 p hg
    simpa only [d462, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d462, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5897 p hg
    simpa only [d462, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5899 (p : Pattern) (guard : d1092 p = 1) : d58 p ≤ (0 : Int) + d393 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5703 p hg
    simpa only [d1092, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4899 p hg
    simpa only [d1092, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5900 (p : Pattern) (guard : d1092 p = 1) : d463 p ≤ (0 : Int) + d394 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d463, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5892 p hg
    simpa only [d463, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d463, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5899 p hg
    simpa only [d463, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5901 (p : Pattern) (guard : d1092 p = 1) : d465 p ≤ (0 : Int) + d395 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d465, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5708 p hg
    simpa only [d1092, d465, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d465, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4902 p hg
    simpa only [d1092, d465, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5902 (p : Pattern) (guard : d1092 p = 1) : d466 p ≤ (0 : Int) + d396 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d466, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5901 p hg
    simpa only [d466, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d466, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5896 p hg
    simpa only [d466, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5903 (p : Pattern) (guard : d1092 p = 1) : d467 p ≤ (0 : Int) + d397 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d467, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5900 p hg
    simpa only [d467, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d467, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5902 p hg
    simpa only [d467, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5904 (p : Pattern) (guard : d1092 p = 1) : d468 p ≤ (0 : Int) + d398 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d468, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5898 p hg
    simpa only [d468, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d468, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5903 p hg
    simpa only [d468, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5905 (p : Pattern) (guard : d1092 p = 1) : d460 p ≤ (0 : Int) + d399 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d460, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5718 p hg
    simpa only [d1092, d460, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d460, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d1092, d460, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5906 (p : Pattern) (guard : d1092 p = 1) : d52 p ≤ (0 : Int) + d399 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5686 p hg
    simpa only [d1092, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d1092, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5907 (p : Pattern) (guard : d1092 p = 1) : d469 p ≤ (0 : Int) + d399 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5905 p hg
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5906 p hg
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5908 (p : Pattern) (guard : d1092 p = 1) : d54 p ≤ (0 : Int) + d400 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5698 p hg
    simpa only [d1092, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4895 p hg
    simpa only [d1092, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5909 (p : Pattern) (guard : d1092 p = 1) : d470 p ≤ (0 : Int) + d401 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d470, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5906 p hg
    simpa only [d470, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d470, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5908 p hg
    simpa only [d470, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5910 (p : Pattern) (guard : d1092 p = 1) : d471 p ≤ (0 : Int) + d402 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d471, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5907 p hg
    simpa only [d471, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d471, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5909 p hg
    simpa only [d471, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5911 (p : Pattern) (guard : d1092 p = 1) : d58 p ≤ (0 : Int) + d403 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5704 p hg
    simpa only [d1092, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4899 p hg
    simpa only [d1092, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5912 (p : Pattern) (guard : d1092 p = 1) : d472 p ≤ (0 : Int) + d404 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d472, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5905 p hg
    simpa only [d472, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d472, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5911 p hg
    simpa only [d472, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5913 (p : Pattern) (guard : d1092 p = 1) : d61 p ≤ (0 : Int) + d405 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5710 p hg
    simpa only [d1092, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4902 p hg
    simpa only [d1092, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5914 (p : Pattern) (guard : d1092 p = 1) : d473 p ≤ (0 : Int) + d406 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d473, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5913 p hg
    simpa only [d473, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d473, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5908 p hg
    simpa only [d473, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5915 (p : Pattern) (guard : d1092 p = 1) : d474 p ≤ (0 : Int) + d407 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d474, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5912 p hg
    simpa only [d474, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d474, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5914 p hg
    simpa only [d474, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5916 (p : Pattern) (guard : d1092 p = 1) : d475 p ≤ (0 : Int) + d408 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d475, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5910 p hg
    simpa only [d475, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d475, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5915 p hg
    simpa only [d475, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5917 (p : Pattern) (guard : d1092 p = 1) : d476 p ≤ (0 : Int) + d409 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d476, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5904 p hg
    simpa only [d476, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d476, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5916 p hg
    simpa only [d476, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5918 (p : Pattern) (guard : d1092 p = 1) : d477 p ≤ (0 : Int) + d391 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d477, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5892 p hg
    simpa only [d477, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d477, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5896 p hg
    simpa only [d477, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5919 (p : Pattern) (guard : d1092 p = 1) : d479 p ≤ (0 : Int) + d410 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d479, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5732 p hg
    simpa only [d1092, d479, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d479, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1451 p hg
    simpa only [d1092, d479, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5920 (p : Pattern) (guard : d1092 p = 1) : d70 p ≤ (0 : Int) + d411 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5734 p hg
    simpa only [d1092, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare882 p hg
    simpa only [d1092, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5921 (p : Pattern) (guard : d1092 p = 1) : d480 p ≤ (0 : Int) + d412 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d480, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5919 p hg
    simpa only [d480, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d480, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5920 p hg
    simpa only [d480, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5922 (p : Pattern) (guard : d1092 p = 1) : d481 p ≤ (0 : Int) + d413 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d481, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5918 p hg
    simpa only [d481, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d481, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5921 p hg
    simpa only [d481, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5923 (p : Pattern) (guard : d1092 p = 1) : d482 p ≤ (0 : Int) + d414 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d482, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5898 p hg
    simpa only [d482, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d482, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5922 p hg
    simpa only [d482, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5924 (p : Pattern) (guard : d1092 p = 1) : d484 p ≤ (0 : Int) + d389 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d484, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5767 p hg
    simpa only [d1092, d484, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d484, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4893 p hg
    simpa only [d1092, d484, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5925 (p : Pattern) (guard : d1092 p = 1) : d485 p ≤ (0 : Int) + d391 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d485, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5924 p hg
    simpa only [d485, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d485, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5896 p hg
    simpa only [d485, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5926 (p : Pattern) (guard : d1092 p = 1) : d486 p ≤ (0 : Int) + d415 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d486, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5925 p hg
    simpa only [d486, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d486, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2080 p hg
    simpa only [d486, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5927 (p : Pattern) (guard : d1092 p = 1) : d487 p ≤ (0 : Int) + d416 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d487, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5898 p hg
    simpa only [d487, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d487, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5926 p hg
    simpa only [d487, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5928 (p : Pattern) (guard : d1092 p = 1) : d488 p ≤ (0 : Int) + d417 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d488, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5923 p hg
    simpa only [d488, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d488, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5927 p hg
    simpa only [d488, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5929 (p : Pattern) (guard : d1092 p = 1) : d461 p ≤ (0 : Int) + d401 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d461, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5905 p hg
    simpa only [d461, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d461, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5908 p hg
    simpa only [d461, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5930 (p : Pattern) (guard : d1092 p = 1) : d489 p ≤ (0 : Int) + d418 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d489, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5929 p hg
    simpa only [d489, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d489, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2080 p hg
    simpa only [d489, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5931 (p : Pattern) (guard : d1092 p = 1) : d490 p ≤ (0 : Int) + d419 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d490, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5910 p hg
    simpa only [d490, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d490, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5930 p hg
    simpa only [d490, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5932 (p : Pattern) (guard : d1092 p = 1) : d491 p ≤ (0 : Int) + d418 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d491, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5909 p hg
    simpa only [d491, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d491, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2080 p hg
    simpa only [d491, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5933 (p : Pattern) (guard : d1092 p = 1) : d492 p ≤ (0 : Int) + d419 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d492, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5910 p hg
    simpa only [d492, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d492, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5932 p hg
    simpa only [d492, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5934 (p : Pattern) (guard : d1092 p = 1) : d493 p ≤ (0 : Int) + d419 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5931 p hg
    simpa only [d493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5933 p hg
    simpa only [d493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5935 (p : Pattern) (guard : d1092 p = 1) : d494 p ≤ (0 : Int) + d420 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d494, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5928 p hg
    simpa only [d494, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d494, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5934 p hg
    simpa only [d494, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5936 (p : Pattern) (guard : d1092 p = 1) : d495 p ≤ (0 : Int) + d421 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d495, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5917 p hg
    simpa only [d495, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d495, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5935 p hg
    simpa only [d495, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5937 (p : Pattern) (guard : d1092 p = 1) : d496 p ≤ (0 : Int) + d394 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d496, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5924 p hg
    simpa only [d496, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d496, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5899 p hg
    simpa only [d496, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5938 (p : Pattern) (guard : d1092 p = 1) : d61 p ≤ (0 : Int) + d395 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5791 p hg
    simpa only [d1092, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4902 p hg
    simpa only [d1092, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5939 (p : Pattern) (guard : d1092 p = 1) : d473 p ≤ (0 : Int) + d396 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d473, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5938 p hg
    simpa only [d473, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d473, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5896 p hg
    simpa only [d473, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5940 (p : Pattern) (guard : d1092 p = 1) : d497 p ≤ (0 : Int) + d397 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d497, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5937 p hg
    simpa only [d497, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d497, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5939 p hg
    simpa only [d497, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5941 (p : Pattern) (guard : d1092 p = 1) : d498 p ≤ (0 : Int) + d398 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d498, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5898 p hg
    simpa only [d498, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d498, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5940 p hg
    simpa only [d498, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5942 (p : Pattern) (guard : d1092 p = 1) : d499 p ≤ (0 : Int) + d398 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5904 p hg
    simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5941 p hg
    simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5943 (p : Pattern) (guard : d1092 p = 1) : d501 p ≤ (0 : Int) + d422 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d501, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5750 p hg
    simpa only [d1092, d501, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d501, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare919 p hg
    simpa only [d1092, d501, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5944 (p : Pattern) (guard : d1092 p = 1) : d97 p ≤ (0 : Int) + d422 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5752 p hg
    simpa only [d1092, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare919 p hg
    simpa only [d1092, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5945 (p : Pattern) (guard : d1092 p = 1) : d502 p ≤ (0 : Int) + d422 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5943 p hg
    simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5944 p hg
    simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5946 (p : Pattern) (guard : d1092 p = 1) : d109 p ≤ (0 : Int) + d423 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d109, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5944 p hg
    simpa only [d109, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d109, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5920 p hg
    simpa only [d109, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5947 (p : Pattern) (guard : d1092 p = 1) : d503 p ≤ (0 : Int) + d424 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d503, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5945 p hg
    simpa only [d503, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d503, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5946 p hg
    simpa only [d503, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5948 (p : Pattern) (guard : d1092 p = 1) : d504 p ≤ (0 : Int) + d423 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d504, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5943 p hg
    simpa only [d504, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d504, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5920 p hg
    simpa only [d504, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5949 (p : Pattern) (guard : d1092 p = 1) : d68 p ≤ (0 : Int) + d410 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5758 p hg
    simpa only [d1092, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1451 p hg
    simpa only [d1092, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5950 (p : Pattern) (guard : d1092 p = 1) : d75 p ≤ (0 : Int) + d412 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d75, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5949 p hg
    simpa only [d75, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d75, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5920 p hg
    simpa only [d75, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5951 (p : Pattern) (guard : d1092 p = 1) : d505 p ≤ (0 : Int) + d425 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d505, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5948 p hg
    simpa only [d505, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d505, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5950 p hg
    simpa only [d505, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5952 (p : Pattern) (guard : d1092 p = 1) : d506 p ≤ (0 : Int) + d426 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d506, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5947 p hg
    simpa only [d506, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d506, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5951 p hg
    simpa only [d506, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5953 (p : Pattern) (guard : d1092 p = 1) : d125 p ≤ (0 : Int) + d425 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d125, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5946 p hg
    simpa only [d125, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d125, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5950 p hg
    simpa only [d125, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5954 (p : Pattern) (guard : d1092 p = 1) : d507 p ≤ (0 : Int) + d426 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d507, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5947 p hg
    simpa only [d507, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d507, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5953 p hg
    simpa only [d507, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5955 (p : Pattern) (guard : d1092 p = 1) : d508 p ≤ (0 : Int) + d426 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5952 p hg
    simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5954 p hg
    simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5956 (p : Pattern) (guard : d1092 p = 1) : d509 p ≤ (0 : Int) + d427 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d509, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5942 p hg
    simpa only [d509, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d509, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5955 p hg
    simpa only [d509, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5957 (p : Pattern) (guard : d1092 p = 1) : d510 p ≤ (0 : Int) + d389 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5924 p hg
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5893 p hg
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5958 (p : Pattern) (guard : d1092 p = 1) : d470 p ≤ (0 : Int) + d391 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d470, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5893 p hg
    simpa only [d470, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d470, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5896 p hg
    simpa only [d470, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5959 (p : Pattern) (guard : d1092 p = 1) : d511 p ≤ (0 : Int) + d392 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d511, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5957 p hg
    simpa only [d511, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d511, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5958 p hg
    simpa only [d511, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5960 (p : Pattern) (guard : d1092 p = 1) : d491 p ≤ (0 : Int) + d415 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d491, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5958 p hg
    simpa only [d491, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d491, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2080 p hg
    simpa only [d491, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5961 (p : Pattern) (guard : d1092 p = 1) : d512 p ≤ (0 : Int) + d416 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d512, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5959 p hg
    simpa only [d512, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d512, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5960 p hg
    simpa only [d512, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5962 (p : Pattern) (guard : d1092 p = 1) : d513 p ≤ (0 : Int) + d416 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5927 p hg
    simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5961 p hg
    simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5963 (p : Pattern) (guard : d1092 p = 1) : d111 p ≤ (0 : Int) + d428 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d111, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5946 p hg
    simpa only [d111, d428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d111, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2105 p hg
    simpa only [d111, d428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5964 (p : Pattern) (guard : d1092 p = 1) : d514 p ≤ (0 : Int) + d429 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d514, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5947 p hg
    simpa only [d514, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d514, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5963 p hg
    simpa only [d514, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5965 (p : Pattern) (guard : d1092 p = 1) : d515 p ≤ (0 : Int) + d435 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d515, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5964 p hg
    simpa only [d515, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d515, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2131 p hg
    simpa only [d515, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5966 (p : Pattern) (guard : d1092 p = 1) : d516 p ≤ (0 : Int) + d436 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d516, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5962 p hg
    simpa only [d516, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d516, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5965 p hg
    simpa only [d516, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5967 (p : Pattern) (guard : d1092 p = 1) : d517 p ≤ (0 : Int) + d437 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d517, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5956 p hg
    simpa only [d517, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d517, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5966 p hg
    simpa only [d517, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5968 (p : Pattern) (guard : d1092 p = 1) : d518 p ≤ (0 : Int) + d438 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d518, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5936 p hg
    simpa only [d518, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d518, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5967 p hg
    simpa only [d518, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5969 (p : Pattern) (guard : d1092 p = 1) : d519 p ≤ (0 : Int) + d404 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d519, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5906 p hg
    simpa only [d519, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d519, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5911 p hg
    simpa only [d519, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5970 (p : Pattern) (guard : d1092 p = 1) : d520 p ≤ (0 : Int) + d407 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d520, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5969 p hg
    simpa only [d520, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d520, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5914 p hg
    simpa only [d520, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5971 (p : Pattern) (guard : d1092 p = 1) : d521 p ≤ (0 : Int) + d408 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d521, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5910 p hg
    simpa only [d521, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d521, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5970 p hg
    simpa only [d521, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5972 (p : Pattern) (guard : d1092 p = 1) : d522 p ≤ (0 : Int) + d408 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5916 p hg
    simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5971 p hg
    simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5973 (p : Pattern) (guard : d1092 p = 1) : d523 p ≤ (0 : Int) + d409 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d523, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5942 p hg
    simpa only [d523, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d523, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5972 p hg
    simpa only [d523, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5974 (p : Pattern) (guard : d1092 p = 1) : d524 p ≤ (0 : Int) + d402 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d524, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5906 p hg
    simpa only [d524, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d524, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5909 p hg
    simpa only [d524, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5975 (p : Pattern) (guard : d1092 p = 1) : d525 p ≤ (0 : Int) + d419 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d525, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5974 p hg
    simpa only [d525, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d525, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5932 p hg
    simpa only [d525, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5976 (p : Pattern) (guard : d1092 p = 1) : d526 p ≤ (0 : Int) + d419 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5933 p hg
    simpa only [d526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5975 p hg
    simpa only [d526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5977 (p : Pattern) (guard : d1092 p = 1) : d527 p ≤ (0 : Int) + d439 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d527, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5962 p hg
    simpa only [d527, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d527, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5976 p hg
    simpa only [d527, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5978 (p : Pattern) (guard : d1092 p = 1) : d528 p ≤ (0 : Int) + d440 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d528, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5973 p hg
    simpa only [d528, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d528, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5977 p hg
    simpa only [d528, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5979 (p : Pattern) (guard : d1092 p = 1) : d58 p ≤ (0 : Int) + d441 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1092, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5877 p hg
    simpa only [d1092, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4899 p hg
    simpa only [d1092, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5980 (p : Pattern) (guard : d1092 p = 1) : d519 p ≤ (0 : Int) + d442 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d519, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5893 p hg
    simpa only [d519, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d519, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5979 p hg
    simpa only [d519, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5981 (p : Pattern) (guard : d1092 p = 1) : d520 p ≤ (0 : Int) + d443 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d520, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5980 p hg
    simpa only [d520, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d520, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5939 p hg
    simpa only [d520, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5982 (p : Pattern) (guard : d1092 p = 1) : d529 p ≤ (0 : Int) + d444 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d529, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5959 p hg
    simpa only [d529, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d529, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5981 p hg
    simpa only [d529, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5983 (p : Pattern) (guard : d1092 p = 1) : d530 p ≤ (0 : Int) + d445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d530, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5941 p hg
    simpa only [d530, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d530, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5982 p hg
    simpa only [d530, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5984 (p : Pattern) (guard : d1092 p = 1) : d125 p ≤ (0 : Int) + d446 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d125, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2128 p hg
    simpa only [d125, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d125, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2080 p hg
    simpa only [d125, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5985 (p : Pattern) (guard : d1092 p = 1) : d126 p ≤ (0 : Int) + d447 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d126, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2129 p hg
    simpa only [d126, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d126, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5984 p hg
    simpa only [d126, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5986 (p : Pattern) (guard : d1092 p = 1) : d531 p ≤ (0 : Int) + d448 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d531, d448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5954 p hg
    simpa only [d531, d448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d531, d448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5985 p hg
    simpa only [d531, d448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5987 (p : Pattern) (guard : d1092 p = 1) : d532 p ≤ (0 : Int) + d449 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d532, d449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5983 p hg
    simpa only [d532, d449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d532, d449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5986 p hg
    simpa only [d532, d449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5988 (p : Pattern) (guard : d1092 p = 1) : d533 p ≤ (0 : Int) + d450 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d533, d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5961 p hg
    simpa only [d533, d450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d533, d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5975 p hg
    simpa only [d533, d450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5989 (p : Pattern) (guard : d1092 p = 1) : d130 p ≤ (0 : Int) + d451 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d130, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2131 p hg
    simpa only [d130, d451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d130, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2105 p hg
    simpa only [d130, d451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5990 (p : Pattern) (guard : d1092 p = 1) : d534 p ≤ (0 : Int) + d452 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d534, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5988 p hg
    simpa only [d534, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d534, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5989 p hg
    simpa only [d534, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5991 (p : Pattern) (guard : d1092 p = 1) : d535 p ≤ (0 : Int) + d453 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d535, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5987 p hg
    simpa only [d535, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d535, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5990 p hg
    simpa only [d535, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5992 (p : Pattern) (guard : d1092 p = 1) : d536 p ≤ (0 : Int) + d454 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d536, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5978 p hg
    simpa only [d536, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d536, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5991 p hg
    simpa only [d536, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5993 (p : Pattern) (guard : d1092 p = 1) : d537 p ≤ (0 : Int) + d455 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d537, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5968 p hg
    simpa only [d537, d455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d537, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5992 p hg
    simpa only [d537, d455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5994 (p : Pattern) (guard : d0 p = 1) : d456 p ≤ (0 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5995 (p : Pattern) (guard : d1365 p = 1) : d457 p ≤ (0 : Int) + d8 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5994 p hg
    simpa only [d1365, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5689 p hg
    simpa only [d1365, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5996 (p : Pattern) (guard : d0 p = 1) : d52 p ≤ (0 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5997 (p : Pattern) (guard : d1365 p = 1) : d52 p ≤ (0 : Int) + d8 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5996 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5689 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5998 (p : Pattern) (guard : d1365 p = 1) : d458 p ≤ (0 : Int) + d8 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5995 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5997 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5999 (p : Pattern) (guard : d0 p = 1) : d459 p ≤ (0 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6000 (p : Pattern) (guard : d1365 p = 1) : d460 p ≤ (0 : Int) + d8 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5999 p hg
    simpa only [d1365, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5689 p hg
    simpa only [d1365, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6001 (p : Pattern) (guard : d0 p = 1) : d54 p ≤ (0 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6002 (p : Pattern) (guard : d1365 p = 1) : d54 p ≤ (0 : Int) + d20 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6001 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5696 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6003 (p : Pattern) (guard : d1365 p = 1) : d461 p ≤ (0 : Int) + d1097 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d461, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6000 p hg
    simpa only [d461, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d461, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6002 p hg
    simpa only [d461, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6004 (p : Pattern) (guard : d1365 p = 1) : d462 p ≤ (0 : Int) + d1098 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d462, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5998 p hg
    simpa only [d462, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d462, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6003 p hg
    simpa only [d462, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6005 (p : Pattern) (guard : d0 p = 1) : d58 p ≤ (0 : Int) + d33 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6006 (p : Pattern) (guard : d1365 p = 1) : d58 p ≤ (0 : Int) + d33 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6005 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5703 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6007 (p : Pattern) (guard : d1365 p = 1) : d463 p ≤ (0 : Int) + d1099 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d463, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5995 p hg
    simpa only [d463, d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d463, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6006 p hg
    simpa only [d463, d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6008 (p : Pattern) (guard : d0 p = 1) : d464 p ≤ (0 : Int) + d38 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6009 (p : Pattern) (guard : d1365 p = 1) : d465 p ≤ (0 : Int) + d38 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6008 p hg
    simpa only [d1365, d465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5791 p hg
    simpa only [d1365, d465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6010 (p : Pattern) (guard : d1365 p = 1) : d466 p ≤ (0 : Int) + d1100 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d466, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6009 p hg
    simpa only [d466, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d466, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6002 p hg
    simpa only [d466, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6011 (p : Pattern) (guard : d1365 p = 1) : d467 p ≤ (0 : Int) + d1101 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d467, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6007 p hg
    simpa only [d467, d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d467, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6010 p hg
    simpa only [d467, d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6012 (p : Pattern) (guard : d1365 p = 1) : d468 p ≤ (0 : Int) + d1102 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d468, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6004 p hg
    simpa only [d468, d1102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d468, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6011 p hg
    simpa only [d468, d1102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6013 (p : Pattern) (guard : d0 p = 1) : d459 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare6014 (p : Pattern) (guard : d1365 p = 1) : d460 p ≤ (0 : Int) + d15 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6013 p hg
    simpa only [d1365, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5686 p hg
    simpa only [d1365, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6015 (p : Pattern) (guard : d1365 p = 1) : d52 p ≤ (0 : Int) + d15 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare438 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5686 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6016 (p : Pattern) (guard : d1365 p = 1) : d469 p ≤ (0 : Int) + d15 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6014 p hg
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6015 p hg
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6017 (p : Pattern) (guard : d1365 p = 1) : d54 p ≤ (0 : Int) + d25 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare440 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5698 p hg
    simpa only [d1365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6018 (p : Pattern) (guard : d1365 p = 1) : d470 p ≤ (0 : Int) + d46 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d470, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6015 p hg
    simpa only [d470, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d470, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6017 p hg
    simpa only [d470, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare6019 (p : Pattern) (guard : d1365 p = 1) : d471 p ≤ (0 : Int) + d47 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1365 p = 1 := by simpa only [d471, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6016 p hg
    simpa only [d471, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1365 p = 1 := by simpa only [d471, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6018 p hg
    simpa only [d471, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
